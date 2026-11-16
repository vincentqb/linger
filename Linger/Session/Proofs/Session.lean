module

import all Linger.Session.CoreCode
import all Terminal.CoreCode.Vt
import all Terminal.CoreCode.Mediation
import all Linger.Session.CoreCode.Wire
import all Terminal.CoreCode.Render
-- The `Vt` seal makes the proof layer module-private, so the rungs this file
-- composes arrive through `import all`.
import all Terminal.Proofs.Mediation
import all Terminal.Proofs.Render
import all Linger.Session.Proofs.Wire
-- `Linger.Session.Proofs.Checkpoint` is here for the decoder's door: `Checkpoint.load_live` and
-- `Checkpoint.loadBytes_live` make `LiveVt` provable for a *resumed* daemon (the section
-- "Resume at the daemon", below), and `Checkpoint.loadBytes_saveBytes_live` gives a resumed
-- session's checkpoint round trip (`run_resume_load_save`).
import all Linger.Session.Proofs.Checkpoint
public import Linger.Session.CoreSpec

/-! # The daemon state machine theorems

**Friend module**: `import all Linger.Session` is
what lets these statements name `State`'s private bookkeeping fields — the
`outSeq`/`lookSeq` pair, `dirty` — and its private helpers, which no plain
importer, the daemon included, can reach; a plain importer reads `clients` and `scan` but
can never poke or forge a state. No blanket
`public section`, for the Buf-friend reasons: statements naming private fields
cannot be public, `Linger/Session/Proofs/Driver.lean` and `Theorems/Solution.lean` import
them with `import all`, and module-private is what keeps the `:= rfl`
proofs elaborating in the private scope.

Proved here:
* Sessions outlive clients. A session with zero clients still
  advances (output is never gated on attachment); a client detaching
  (or `detach-all`) cannot change the screen; attach touches only the
  dimensions, never the scrollback.
* The session bounds — the session layer adds four bounded components on top of
  Vt's: the client list (≤ `maxClients`), the label table
  (≤ `maxFields`), a wire decoder per client (≤ the decoder's cap, never
  errored — a malformed peer is closed, not buffered) and the terminal
  scanner (`Bounded.scanOk`). `step` preserves all four against any
  event stream; `Bounded` is the `Bounds` that `run_total_safe` (`Challenge.lean`, part 5)
  states.
* An `unknown` wire message is refused with an error reply and produces no state change
  (`onMsg_unknown`; `step_unknown_refused`, part 5).
-/

namespace Linger.Session

open Terminal
open Linger.Session.Wire (Msg)
open Terminal.Replay (Plan)

attribute [local grind] controlResize resizeOwned resize State.setClient

/-! ## Unknown messages and other exact-shape facts -/

/-- A message this version does not know is a request it cannot serve: the session refuses it
and changes nothing. -/
theorem onMsg_unknown (s : State) (c : Client) (t : UInt8) (p : List UInt8) :
    onMsg s c (.unknown t p) = (s, [.send c.id (.err "unknown message".toUTF8.toList)]) := rfl

/-- Every `info` reply reports the protocol level and the version the daemon runs. -/
theorem infoFields_protocol (s : State) :
    ("protocol", toString Wire.protocol) ∈ infoFields s ∧
      ("version", Terminal.Mediation.versionNumber) ∈ infoFields s := by
  simp [infoFields]

/-- What the name's end record publishes is what `info` reports: a summary that reads the record
sees the daemon's own `fresh`, `unseen` and `asks`. -/
theorem infoFields_seen (s : State) :
    ("fresh", toString s.seen.fresh) ∈ infoFields s ∧
      ("unseen", toString s.seen.unseen) ∈ infoFields s ∧
      ("asks", toString s.seen.asks) ∈ infoFields s := by
  simp [infoFields, State.seen]

/-- Distinct numbers print differently. -/
theorem toString_nat_inj {a b : Nat} (h : toString a = toString b) : a = b := by
  have digits : Nat.toDigits 10 a = Nat.toDigits 10 b := by
    rw [← Nat.toList_repr, ← Nat.toList_repr, ← Nat.toString_eq_repr, ← Nat.toString_eq_repr, h]
  rw [← Nat.ofDigitChars_ten_toDigits (n := a), ← Nat.ofDigitChars_ten_toDigits (n := b), digits]

/-- **Two endings never read the same in `info`**: an exit code, a signal and an ending linger
did not see each give different fields, whatever their numbers. -/
theorem outcomeFields_injective {o₁ o₂ : Outcome} (h : outcomeFields o₁ = outcomeFields o₂) :
    o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [outcomeFields, List.cons.injEq, Prod.mk.injEq] at h
  all_goals
    first
    | rfl
    | exact congrArg _ (UInt8.toNat_inj.mp (toString_nat_inj h.1.2))
    | exact congrArg _ (UInt8.toNat_inj.mp (toString_nat_inj h.2.1.2))
    | exact absurd h (by simp)

/-- **Two session endings never read the same in `info`**: a saved session's fields have no
`exit`, which every ending of a program has, and name the signal that stopped its daemon. -/
theorem endingFields_injective {e₁ e₂ : Ending} (h : endingFields e₁ = endingFields e₂) :
    e₁ = e₂ := by
  cases e₁ with
  | program o₁ =>
    cases e₂ with
    | program o₂ => exact congrArg _ (outcomeFields_injective h)
    | saved n₂ => cases o₁ <;> simp [endingFields, outcomeFields] at h
    | dismissed => cases o₁ <;> simp [endingFields, outcomeFields] at h
  | saved n₁ =>
    cases e₂ with
    | program o₂ => cases o₂ <;> simp [endingFields, outcomeFields] at h
    | saved
      n₂ =>
      simp only [endingFields, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
      exact congrArg _ (UInt8.toNat_inj.mp (toString_nat_inj h))
    | dismissed => simp [endingFields] at h
  | dismissed =>
    cases e₂ with
    | program o₂ => cases o₂ <;> simp [endingFields, outcomeFields] at h
    | saved n₂ => simp [endingFields] at h
    | dismissed => rfl

/-- What an ending tells a client is how its program ended, the status a shell would report, or
the signal that stopped the daemon: no rendered frame, and nothing a daemon serves. -/
theorem told_mem {e : Ending} {m : Msg} (h : m ∈ e.told) :
    (∃ o, m = .ended o) ∨ (∃ status, m = .exited status) ∨ ∃ signal, m = .saved signal := by
  cases e with
  | program o =>
    simp only [Ending.told] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl ⟨_, rfl⟩
    · rcases List.mem_singleton.mp h with rfl
      exact .inr (.inl ⟨_, rfl⟩)
  | saved n =>
    simp only [Ending.told] at h
    rcases List.mem_singleton.mp h with rfl
    exact .inr (.inr ⟨_, rfl⟩)
  | dismissed => simp [Ending.told] at h

/-- A daemon's signal pipe stops it only when it carried one of `stopSignals`. -/
theorem stopOf_none (bytes : List UInt8) : stopOf bytes = none ↔ ∀ b ∈ bytes, b ∉ stopSignals := by
  simp [stopOf, List.find?_eq_none]

/-- The first stop signal the pipe carried stops the daemon, and ends the session before a child's
end that came after it… -/
theorem stopOf_first (signal : UInt8) (rest : List UInt8) (stop : signal ∈ stopSignals) :
    stopOf (signal :: rest) = some (signal, true) := by
  simp only [stopSignals, List.mem_cons, List.not_mem_nil, or_false] at stop
  rcases stop with rfl | rfl | rfl | rfl <;> rfl

/-- …but after one that came before it. -/
theorem stopOf_after (signal : UInt8) (rest : List UInt8) (stop : signal ∈ stopSignals) :
    stopOf (0 :: signal :: rest) = some (signal, false) := by
  simp only [stopSignals, List.mem_cons, List.not_mem_nil, or_false] at stop
  rcases stop with rfl | rfl | rfl | rfl <;> rfl

/-- Wrong-direction messages are no request, and are dropped. -/
theorem onMsg_wrong_direction (s : State) (c : Client) (bs : List UInt8) :
    onMsg s c (.output bs) = (s, []) ∧
      onMsg s c (.infoReply bs) = (s, []) ∧
      onMsg s c (.err bs) = (s, []) ∧ onMsg s c .done = (s, []) := ⟨rfl, rfl, rfl, rfl⟩

/-- Info records the read's one answer, leaves the rest of the state alone and
uses the bounded reply producer. -/
theorem onMsg_info (s : State) (c : Client) (ha : c.answered = false) :
    onMsg s c .info = (s.setClient { c with answered := true }, infoMsgs c.id (infoText s)) := by
  simp [onMsg, ha]

/-- **One request per read.** After the read's answer, a further `info`, `history`
or `screen` changes nothing and is refused, so one read builds at most one reply. -/
theorem onMsg_answered (s : State) (c : Client) (m : Msg) (ha : c.answered = true)
    (hm : m = .info ∨ m = .history ∨ m = .screen) :
    onMsg s c m = (s, [.send c.id (.err "one request per read".toUTF8.toList)]) := by
  rcases hm with rfl | rfl | rfl <;> simp [onMsg, ha]

@[simp]
theorem infoMsgs_no_resize (id : Nat) (bs : List UInt8) (cols rows : UInt32) :
    Effect.resizePty cols rows ∉ infoMsgs id bs := by
  unfold infoMsgs
  split <;> simp

/-! ## Describing

`.describe` is pinned three ways — the cap (`onMsg_fields_le`), the forged-record channel
(`infoText_records`) and the exact shape below: for a writable connection it replaces the
description, or removes it for an empty text, keeps every other field, and answers `.done`. -/

/-- **`linger describe` sets exactly the description.** `rfl`-shaped, so a smuggled side
effect — a vt touch, an append to another field — breaks it. -/
theorem onMsg_describe (s : State) (c : Client) (text : List UInt8) (control : c.mode = .writable)
    (fits :
      (s.fields.filter (·.1 != "description") ++
            if descriptionText text = "" then []
            else [("description", descriptionText text)]).length ≤
        maxFields) :
    onMsg s c (.describe text) =
      ({ s with
          fields :=
            s.fields.filter (·.1 != "description") ++
              if descriptionText text = "" then [] else [("description", descriptionText text)],
          dirty := true },
        [.send c.id .done]) := by
  simp only [onMsg, control]
  simp_all [String.isEmpty_iff]

/-! ## Detach: sessions outlive their clients -/

/-- Last-attacher detection uses the old roster; dirty state is saved exactly
once even when the bytes handler removes a malformed peer immediately, after any focus report
the leaver owes the program. -/
theorem closeClient_last_dirty (s : State) (id : Nat) (hd : s.dirty = true)
    (ha : s.clients.any (fun c => c.id == id && c.attached) = true)
    (hl : (s.dropClient id).clients.all (fun c => !c.attached) = true) :
    closeClient s id =
      ({ s.dropClient id with dirty := false },
        focusEffects ((s.client? id).any (·.mode == .writable)) s.focused (s.dropClient id) ++
          [.checkpoint]) := by
  simp [closeClient, hd, ha, hl]

/-- Every effect of a disconnect is a checkpoint or the focus report that tells the program
nobody can type into it any more. -/
theorem closeClient_effects (s : State) (id : Nat) :
    ∀ e ∈ (closeClient s id).2, e = .checkpoint ∨ e = .writePty (focusReport false) :=
  closed_effects s id

/-- Comparing two modes with `==` decides whether they are equal. -/
@[simp]
theorem mode_beq (a b : Mode) : (a == b) = decide (a = b) := rfl

/-- A watcher's disconnect owes the program no focus report: it could not type. -/
theorem closeClient_watcher (s : State) (id : Nat) {c : Client} (hc : s.client? id = some c)
    (hs : c.mode = .readOnly) : ∀ e ∈ (closeClient s id).2, e = .checkpoint := by
  unfold closeClient focusEffects
  simp only [hc, Option.any_some, hs, mode_beq, reduceCtorEq, decide_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, List.nil_append]
  split <;> simp

@[simp]
theorem closeClient_vt (s : State) (id : Nat) : (closeClient s id).1.vt = s.vt := by
  unfold closeClient
  dsimp only
  split <;> rfl

/-- Closing a connection leaves the labels alone. -/
@[simp]
theorem closeClient_labels (s : State) (id : Nat) : (closeClient s id).1.fields = s.fields := by
  unfold closeClient
  dsimp only
  split <;> rfl

/-- A malformed peer takes the same persistence transition as EOF, then asks
the runtime to close its fd. No buffered malformed decoder survives. -/
theorem step_bytes_malformed_close (s : State) (id : Nat) (chunk : List UInt8) (c : Client)
    (hc : s.client? id = some c) (he : (c.decoder.feed chunk).1.errored = true) :
    step s (.bytes id chunk) = ((closeClient s id).1, .close id :: (closeClient s id).2) := by
  simp [step, hc, he]

/-- Closing a client preserves every field except its roster entry and the
dirty flag. Its complete effect list is the focus report the leaver owes the program, if any,
then possibly one checkpoint. The runtime must deliver this event after intentional closes as
well as after EOF; the IO consumer is checked in `Linger.Session.Suites.Attach`. -/
theorem step_closed_frame (s : State) (id : Nat) :
    (step s (.closed id)).1 =
        { s with
          clients := s.clients.filter (·.id != id), dirty := (step s (.closed id)).1.dirty } ∧
      ((step s (.closed id)).2 =
          focusEffects ((s.client? id).any (·.mode == .writable)) s.focused (s.dropClient id) ∨
        (step s (.closed id)).2 =
          focusEffects ((s.client? id).any (·.mode == .writable)) s.focused (s.dropClient id) ++
            [.checkpoint]) := by
  unfold step closeClient
  dsimp only
  split
  · exact ⟨rfl, Or.inr rfl⟩
  · exact ⟨rfl, Or.inl rfl⟩

/-- With zero clients the mediator still advances, and an owned query still
gets its one child-facing reply; only presentation broadcast disappears. -/
theorem step_ptyOut_no_clients (s : State) (chunk : List UInt8) (h : s.clients = []) :
    step s (.ptyOut chunk) =
      let r := Terminal.Mediation.feed s.vt s.scan chunk
      ({ s with
          vt := r.vt, scan := r.scan, dirty := true, outSeq := s.outSeq + 1,
          asking := s.asking || r.asks, notice := r.notice.or s.notice,
          running := (r.marks.foldl hearMark (s.running, s.finished)).1,
          finished := (r.marks.foldl hearMark (s.running, s.finished)).2 },
        if r.replies.isEmpty then [] else [Effect.writePty r.replies]) := by
  simp [step, broadcast, h]

/-- With or without clients, the emulator advances identically to `Vt.feed`. -/
theorem step_ptyOut_vt (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.vt = s.vt.feed chunk := by
  simpa [step] using Terminal.Mediation.feed_vt s.vt s.scan chunk

/-- The one persistent scanner advances exactly once per pty-output event. -/
theorem step_ptyOut_scan (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.scan = (Terminal.Mediation.feed s.vt s.scan chunk).scan := rfl

/-- **No empty output frame.** A chunk that is entirely an owned query leaves no
visible bytes, and `chunksOf n [] = [[]]` — so without `broadcast`'s guard every
terminal query would push a zero-length `output` frame to every attached client.
Stated for an arbitrary roster, since that is where the frames would come from. -/
theorem broadcast_empty (s : State) : broadcast s [] = [] := rfl

/-- A presentation broadcast contains no child write, whatever the roster —
what makes the reply channel and the presentation channel separable. -/
theorem broadcast_no_writePty (s : State) (bytes : List UInt8) :
    (broadcast s bytes).filter
        (fun e =>
          match e with
          | .writePty _ => true
          | _ => false) =
      [] := by
  unfold broadcast outputMsgs
  split <;> simp [List.filter_flatMap, List.filter_map]

/-- The reply prefix depends only on VT, scanner, and bytes; the roster appears
only in the following presentation broadcast. -/
theorem step_ptyOut_effects (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).2 =
      let r := Terminal.Mediation.feed s.vt s.scan chunk
      (if r.replies.isEmpty then [] else [Effect.writePty r.replies]) ++
        broadcast s r.visible := rfl

/-- **The roster-independence claim, stated over `step` so it can fail.** Two
states that agree on the terminal state but have *arbitrarily different client
rosters* prescribe the same zero-or-one child write. Quantifying over `step`
rather than over `Mediation.feed` is the whole point: an earlier version of this
theorem mentioned only `feed`, whose result cannot depend on the roster by
construction, so it stayed true when `.ptyOut` was mutated to gate replies on
`s.clients` — the exact regression it was supposed to guard. -/
theorem ptyOut_reply_roster_independent (s t : State) (chunk : List UInt8) (hv : s.vt = t.vt)
    (hs : s.scan = t.scan) :
    (step s (.ptyOut chunk)).2.filter
        (fun e =>
          match e with
          | .writePty _ => true
          | _ => false) =
      (step t (.ptyOut chunk)).2.filter
        (fun e =>
          match e with
          | .writePty _ => true
          | _ => false) := by
  rw [step_ptyOut_effects, step_ptyOut_effects]
  dsimp only
  rw [hv, hs]
  -- the presentation broadcast contributes no child write, whatever the roster
  rw [List.filter_append, List.filter_append, broadcast_no_writePty, broadcast_no_writePty]

/-- Child exit resets the scanner; `finish`'s pending bytes are broadcast by
`step` before the ending's notifications and close effects. -/
theorem step_childExited_scan (s : State) (outcome : Outcome) :
    (step s (.childExited outcome)).1.scan = .ground := by
  simp [step, conclude, Terminal.Mediation.finish]

/-- However a session ends, the incomplete prefix is the first effect segment, before every
attached or waiting client hears how it ended, then the closes, the end record, the effect that
keeps or discards the session, and daemon exit. -/
theorem conclude_effects (s : State) (ending : Ending) (keep : Bool) :
    (conclude s ending keep).2 =
      let flushed := Terminal.Mediation.finish s.scan
      let s' :=
        { s with
          ended := some ending, scan := flushed.2 }
      let flush := broadcast s' flushed.1
      let notify :=
        s'.clients.filter (fun c => c.attached || c.waiting) |>.flatMap
          (fun c => ending.told.map (Effect.send c.id))
      let closes := s'.clients.map (fun c => Effect.close c.id)
      flush ++ notify ++ closes ++
        [.record ending.record, if keep then .checkpoint else .dropCheckpoint, .exit] := rfl

/-- A program's own end ends the session keeping it, as its result, exactly when nobody attached
sees it end. -/
theorem step_childExited_effects (s : State) (outcome : Outcome) :
    (step s (.childExited outcome)).2 = (conclude s (.program outcome) (!seenBy s.roster)).2 := rfl

/-- A stopped session ends the same way, discarding itself where an unseen ended one is kept. -/
theorem step_stopped_effects (s : State) (outcome : Outcome) :
    (step s (.stopped outcome)).2 = (conclude s (.program outcome) false).2 := rfl

/-- A stop signal stops the program, then ends the session the same way, saved. -/
theorem step_signal_effects (s : State) (signal : UInt8) :
    (step s (.signal signal)).2 = .stopProgram :: (conclude s (.saved signal) true).2 := rfl

/-- …in the state that ending leaves. -/
theorem step_signal_state (s : State) (signal : UInt8) :
    (step s (.signal signal)).1 = (conclude s (.saved signal) true).1 := rfl

/-- An ending leaves the session's terminal as it was: what it saves is the screen it found. -/
theorem conclude_terminal (s : State) (ending : Ending) (keep : Bool) :
    (conclude s ending keep).1.terminal = s.terminal := rfl

/-- A presentation broadcast is only messages to clients. -/
theorem broadcast_sends (s : State) (bytes : List UInt8) :
    ∀ eff ∈ broadcast s bytes, ∃ id m, eff = .send id m := by
  unfold broadcast outputMsgs
  split
  · simp
  · intro eff h
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    exact ⟨_, _, rfl⟩

/-- A presentation broadcast deletes no checkpoint: it is only messages to clients. -/
theorem broadcast_no_dropCheckpoint (s : State) (bytes : List UInt8) :
    Effect.dropCheckpoint ∉ broadcast s bytes := by
  intro h
  obtain ⟨_, _, he⟩ := broadcast_sends s bytes _ h
  cases he

/-- A presentation broadcast saves no checkpoint. -/
theorem broadcast_no_checkpoint (s : State) (bytes : List UInt8) :
    Effect.checkpoint ∉ broadcast s bytes := by
  intro h
  obtain ⟨_, _, he⟩ := broadcast_sends s bytes _ h
  cases he

/-- A presentation broadcast does not stop the daemon. -/
theorem broadcast_no_exit (s : State) (bytes : List UInt8) : Effect.exit ∉ broadcast s bytes := by
  intro h
  obtain ⟨_, _, he⟩ := broadcast_sends s bytes _ h
  cases he

/-- What a function makes of one member is a block of what it makes of the whole list. -/
theorem infix_flatMap_of_mem {α β : Type} {f : α → List β} {l : List α} {a : α} (h : a ∈ l) :
    f a <:+: l.flatMap f := by
  obtain ⟨front, back, rfl⟩ := List.append_of_mem h
  rw [List.flatMap_append, List.flatMap_cons, ← List.append_assoc]
  exact List.infix_append _ _ _

/-- **One ending**: however a session ends, its effects are messages to clients and closes, among
which every client attached or waiting hears how it ended, and then one tail: the end record, the
save that keeps the session or the delete that discards it, as `keep` says, and the exit. -/
theorem conclude_shape (s : State) (ending : Ending) (keep : Bool) :
    ∃ front,
      (conclude s ending keep).2 =
          front ++ [.record ending.record, if keep then .checkpoint else .dropCheckpoint, .exit] ∧
        (∀ eff ∈ front, (∃ id m, eff = .send id m) ∨ ∃ id, eff = .close id) ∧
        ∀ c ∈ s.roster,
          c.attached = true ∨ c.waiting = true → ending.told.map (Effect.send c.id) <:+: front := by
  refine ⟨_, conclude_effects s ending keep, ?_, ?_⟩
  · intro eff h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact .inl (broadcast_sends _ _ _ h)
    · obtain ⟨_, -, h⟩ := List.mem_flatMap.mp h
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
      exact .inl ⟨_, _, rfl⟩
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
      exact .inr ⟨_, rfl⟩
  · intro c hc listening
    have heard : c ∈ s.clients.filter (fun c => c.attached || c.waiting) :=
      List.mem_filter.mpr ⟨hc, by rcases listening with h | h <;> simp [h]⟩
    exact
      (infix_flatMap_of_mem (f := fun c => ending.told.map (Effect.send c.id)) heard).trans
        (List.infix_append _ _ _)

/-- Messages to clients and closes save, delete, record and stop nothing. -/
theorem front_quiet {front : List (Effect Plan)}
    (only : ∀ eff ∈ front, (∃ id m, eff = .send id m) ∨ ∃ id, eff = .close id) :
    Effect.checkpoint ∉ front ∧
      Effect.dropCheckpoint ∉ front ∧
      Effect.exit ∉ front ∧
      Effect.stopProgram ∉ front ∧ ∀ cols rows, Effect.resizePty cols rows ∉ front := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun cols rows h => ?_⟩ <;>
    rcases only _ h with ⟨_, _, he⟩ | ⟨_, he⟩ <;>
    cases he

/-- Nobody attached sees a session end. -/
theorem seenBy_false {roster : List Client} (unseen : ∀ c ∈ roster, c.attached = false) :
    seenBy roster = false := by
  simp only [seenBy, List.any_eq_false]
  intro c hc
  simp [unseen c hc]

/-- An attached client sees a session end. -/
theorem seenBy_true {roster : List Client} {c : Client} (hc : c ∈ roster)
    (attached : c.attached = true) : seenBy roster = true := List.any_eq_true.mpr ⟨c, hc, attached⟩

/-- **An unseen ending is a result**: when the program ends with nobody attached, the daemon saves
the session's last screen, as the program left it, just before it exits, and deletes nothing. So
the session stays listed with how its program ended, and `capture` shows what it left, until the
first attach shows it or `kill` discards it; `kill` itself deletes the checkpoint
(`onMsg_kill`). -/
theorem step_childExited_keeps (s : State) (o : Outcome)
    (unseen : ∀ c ∈ s.roster, c.attached = false) :
    (∃ front,
        (step s (.childExited o)).2 = front ++ [.checkpoint, .exit] ∧
          Effect.dropCheckpoint ∉ front) ∧
      (step s (.childExited o)).1.terminal = s.terminal := by
  obtain ⟨front, effects, only, -⟩ := conclude_shape s (.program o) true
  refine ⟨⟨front ++ [.record (.ended o)], ?_, ?_⟩, rfl⟩
  · rw [step_childExited_effects, seenBy_false unseen, Bool.not_false, effects]
    simp [Ending.record]
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact (front_quiet only).2.1 h
    · simp at h

/-- **A seen ending leaves nothing**: when the program ends while a client is attached, of
either mode, every client attached or waiting is told how it ended, and then the session ends as
a kill ends one: its end record says how the program ended, its checkpoint is deleted and nothing
before that saves one. -/
theorem step_childExited_seen (s : State) (o : Outcome) {c : Client} (hc : c ∈ s.roster)
    (attached : c.attached = true) :
    (∃ front,
        (step s (.childExited o)).2 = front ++ [.record (.ended o), .dropCheckpoint, .exit] ∧
          Effect.checkpoint ∉ front ∧
          ∀ c ∈ s.roster,
            c.attached = true ∨ c.waiting = true →
              (Ending.program o).told.map (Effect.send c.id) <:+: front) ∧
      (step s (.childExited o)).1.terminal = s.terminal := by
  obtain ⟨front, effects, only, heard⟩ := conclude_shape s (.program o) false
  refine ⟨⟨front, ?_, (front_quiet only).1, heard⟩, rfl⟩
  rw [step_childExited_effects, seenBy_true hc attached, Bool.not_true, effects]
  rfl

/-- **A killed session is discarded**: once the daemon has stopped its program, the session ends
as one whose program ended by itself, but its last effect before exit deletes its checkpoint, and
nothing before that saves one. -/
theorem step_stopped_discards (s : State) (o : Outcome) :
    (∃ front,
        (step s (.stopped o)).2 = front ++ [.dropCheckpoint, .exit] ∧ Effect.checkpoint ∉ front) ∧
      (step s (.stopped o)).1.terminal = s.terminal := by
  obtain ⟨front, effects, only, -⟩ := conclude_shape s (.program o) false
  refine ⟨⟨front ++ [.record (.ended o)], ?_, ?_⟩, rfl⟩
  · rw [step_stopped_effects, effects]
    simp [Ending.record]
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact (front_quiet only).1 h
    · simp at h

/-- **A stop signal saves the session**: the daemon stops the program, then every client attached
or waiting hears that the signal stopped the daemon, the end record says so, the screen the signal
found is saved and kept, and the daemon exits; nothing deletes the checkpoint. -/
theorem step_signal_saves (s : State) (signal : UInt8) :
    ∃ front,
      (step s (.signal signal)).2 =
          .stopProgram :: front ++ [.record (.saved signal), .checkpoint, .exit] ∧
        Effect.dropCheckpoint ∉ front ∧
        (∀ c ∈ s.roster,
          c.attached = true ∨ c.waiting = true → Effect.send c.id (.saved signal) ∈ front) ∧
        (step s (.signal signal)).1.terminal = s.terminal := by
  obtain ⟨front, effects, only, heard⟩ := conclude_shape s (.saved signal) true
  refine ⟨front, ?_, (front_quiet only).2.1, fun c hc listening => ?_, rfl⟩
  · rw [step_signal_effects, effects]
    rfl
  · exact (heard c hc listening).subset (by simp [Ending.told])

/-- `kill` from a client that may send it stops the program, whose end then ends the session
(`step_stopped_discards`), and closes its own connection, so nothing it sent after the kill
takes effect; a watcher's is refused and changes nothing. -/
theorem onMsg_kill (s : State) (c : Client) :
    onMsg s c .kill =
      if c.mode == .readOnly then (s, [.send c.id (.err "read-only".toUTF8.toList)])
      else (s, [.stopProgram, .close c.id]) := rfl

/-- However a session ends, the daemon's last effect is its exit. -/
theorem conclude_last (s : State) (ending : Ending) (keep : Bool) :
    (conclude s ending keep).2.getLast? = some .exit := by
  rw [conclude_effects]
  simp

/-- **`detach-all`'s whole purpose, as an equation.** The
verb changes no state at all, so everything it promises lives in the effect
list: one `.close` per *attached* client — the filter is the claim, since a
control connection (`linger send`, `linger info`) must survive a detach-all it
did not ask for — and a `.done` to the requester last, after the closes, so the
caller's own socket is not shut before its reply is queued. `rfl`, so dropping
the filter, reordering the `.done`, or closing the roster instead of the
attached subset each break it. -/
theorem onMsg_detachAll (s : State) (c : Client) (control : c.mode = .writable) :
    onMsg s c .detachAll =
      (s,
        (s.clients.filter (·.attached) |>.map (fun c' => Effect.close c'.id)) ++
          [.send c.id .done]) := by
  simp [onMsg, control]

/-- **A same-size reattach leaves the emulator untouched.** `Vt.resize` resets the
scroll region and tab ruler (`top`/`bot`/`tabs`) unconditionally, so resizing at an
unchanged size would wipe a child's `DECSTBM` and custom tab stops from the model — and
the kernel sends no `SIGWINCH` at an unchanged winsize, so the child would never re-emit
them. The attach handler resizes only on a genuine change, and this is why it is
safe: the whole `vt`, region and ruler included, is preserved. -/
theorem onMsg_attach_same_size_vt (s : State) (c : Client) (mode : Mode) (cols rows : UInt32)
    (hc : s.vt.cols = cols.toNat) (hr : s.vt.rows = rows.toNat) :
    (onMsg s c (.attach mode cols rows)).1.vt = s.vt := by
  unfold onMsg resizeOwned resize
  dsimp only
  split
  · rfl
  · split
    · simp [State.setClient, hc, hr]
    · simp [State.setClient]

/-- A connection gets one replay. Refusing a second attach keeps a decoded
message batch from building a backlog of immutable snapshots. -/
theorem onMsg_attach_already (s : State) (c : Client) (mode : Mode) (cols rows : UInt32)
    (h : c.attached = true) :
    onMsg s c (.attach mode cols rows) =
      (s, [.send c.id (.err "already attached".toUTF8.toList)]) := by
  simp [onMsg, h]

/-- Capture exactly the resulting attach snapshot, after any owned resize.
Later messages may change the runtime's state before it executes this plan. -/
theorem onMsg_attach_snapshot (s : State) (c : Client) (mode : Mode) (cols rows : UInt32)
    (h : c.attached = false) :
    ((onMsg s c (.attach mode cols rows)).2.filterMap
        (fun e =>
          match e with
          | .replay id plan => some (id, plan)
          | _ => none)) =
      [(c.id, Replay.start (onMsg s c (.attach mode cols rows)).1.vt)] := by
  unfold onMsg
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  unfold resizeOwned resize focusEffects
  dsimp only
  repeat' split
  all_goals simp

/-- Keystrokes from a writable client, whatever its terminal's size, go to the pty, not the
emulator: echo is the shell's job, so the machine's screen cannot drift. -/
theorem onMsg_input (s : State) (c : Client) (bs : List UInt8) (h : c.mode = .writable) :
    onMsg s c (.input bs) = (s, [.writePty bs]) := by
  unfold onMsg
  simp [h]

/-- A watcher's keyboard goes nowhere, whatever its terminal's size: neither state nor pty sees
it. -/
theorem onMsg_input_readonly (s : State) (c : Client) (bs : List UInt8) (h : c.mode = .readOnly) :
    onMsg s c (.input bs) = (s, []) := by
  unfold onMsg
  simp [h]

/-! ## The session bounds -/

/-- The composite session bound. `Linger.Session.Bounds` (`Linger/Session/CoreSpec.lean`) states
it through the state's observations; `bounded_iff_bounds` relates the two. -/
structure Bounded (s : State) : Prop where
  clientsLe : s.clients.length ≤ maxClients
  fieldsLe : s.fields.length ≤ maxFields
  decOk : ∀ c ∈ s.clients, c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload
  scanOk : s.scan.Bounded

/-- The private bound and the specification's agree. -/
theorem bounded_iff_bounds (s : State) :
    Bounded s ↔ Bounds State.roster State.fieldList State.scanner s :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

/-! ### The roster cap at the door

`Bounded.clientsLe` names `maxClients`, and `step_bounded` preserves it — but both are
about the invariant *surviving*, and neither says the refusal happens. These two do, and
they are the only statements in the tree about the `.connected` handler. -/

/-- **At the cap, the client is refused loudly and disconnected** — an error frame *and* a
close. Not silently dropped, which would leave a peer waiting on a socket that will never
answer, and not admitted, which would break the cap. -/
theorem step_connected_refused (s : State) (id : Nat) (h : maxClients ≤ s.clients.length) :
    step s (.connected id) =
      (s, [Effect.send id (.err "too many clients".toUTF8.toList), Effect.close id]) := by
  unfold step
  dsimp only
  rw [ite_eq_left (show s.clients.length ≥ maxClients from h)]

/-- **Below the cap it is admitted, and appended.** Append rather than prepend is the whole
of attach ordering: `attachSeq` hands out the size owner role by arrival, so a prepend would
silently make the newest client the oldest. -/
theorem step_connected_admitted (s : State) (id : Nat) (h : s.clients.length < maxClients) :
    step s (.connected id) = ({ s with clients := s.clients ++ [{ id }] }, []) := by
  unfold step
  dsimp only
  rw [ite_eq_right (show ¬(s.clients.length ≥ maxClients) from by omega)]

/-! ### The checkpoint cadence

`ckptIntervalMs` gates the periodic save. The runtime supplies `now`, but the decision is
pure, so what the constant buys is statable here. -/

/-- Below the cadence, or with nothing dirty, a tick checkpoints nothing. -/
theorem step_tick_quiet (s : State) (now : Nat)
    (h : (s.dirty && decide (now ≥ s.lastCkptMs + ckptIntervalMs)) = false) :
    (step s (.tick now)).2 = [] := by simp [step, h]

/-- When it does fire: exactly one checkpoint, and **the clock re-arms to `now`** — which is
what makes the cadence a rate rather than a one-time threshold. -/
theorem step_tick_checkpoint (s : State) (now : Nat)
    (h : (s.dirty && decide (now ≥ s.lastCkptMs + ckptIntervalMs)) = true) :
    (step s (.tick now)).2 = [Effect.checkpoint] ∧ (step s (.tick now)).1.lastCkptMs = now := by
  simp_all [step]

/-- Less than one interval of elapsed time preserves dirty state and the attempt
clock, with no save. This also covers a tick older than the previous attempt. -/
theorem step_tick_before_interval (s : State) (now : Nat)
    (h : now - s.lastCkptMs < ckptIntervalMs) :
    (step s (.tick now)).2 = [] ∧
      (step s (.tick now)).1.lastCkptMs = s.lastCkptMs ∧
      (step s (.tick now)).1.dirty = s.dirty := by
  have htime : ¬now ≥ s.lastCkptMs + ckptIntervalMs := by omega
  simp [step, htime, State.ticked]

/-- Every periodic save has at least one full interval since its previous
attempt, for arbitrary natural-number clocks. -/
theorem step_tick_checkpoint_elapsed (s : State) (now : Nat)
    (h : Effect.checkpoint ∈ (step s (.tick now)).2) : ckptIntervalMs ≤ now - s.lastCkptMs := by
  by_cases early : now - s.lastCkptMs < ckptIntervalMs
  · have quiet := (step_tick_before_interval s now early).1
    simp [quiet] at h
  · omega

/-- A failed save preserves the complete session and attempt clock while
making it retryable. No effect is emitted, so a storage failure cannot spin. -/
theorem step_checkpointFailed (s : State) :
    step s .checkpointFailed = ({ s with dirty := true }, []) := rfl

/-! ### Work follows events

A daemon sleeps until an event or its session's next tick (`State.nextTick`). These say when a
session needs a tick: only while it has unsaved changes or fresh output, and never later than
the cadence or the freshness window require. -/

/-- A tick records when the last output it saw arrived and whether that is still fresh, and
changes nothing else the session holds: its screen, roster, labels and unsaved changes. -/
theorem ticked_frame (s : State) (now : Nat) :
    (s.ticked now).vt = s.vt ∧
      (s.ticked now).clients = s.clients ∧
      (s.ticked now).fields = s.fields ∧
      (s.ticked now).dirty = s.dirty ∧
      (s.ticked now).lastOutMs = (if s.tickOutSeq < s.outSeq then some now else s.lastOutMs) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A session needs a tick exactly while it has unsaved changes or fresh output. -/
theorem nextTick_eq_none (s : State) :
    s.nextTick = none ↔ s.dirty = false ∧ (s.freshFlag = false ∨ s.lastOutMs = none) := by
  unfold State.nextTick
  cases s.dirty <;> cases s.freshFlag <;> cases s.lastOutMs <;> simp

/-- Unsaved changes get their tick no later than the cadence allows a save. -/
theorem nextTick_save (s : State) (h : s.dirty = true) :
    ∃ due, s.nextTick = some due ∧ due ≤ s.lastCkptMs + ckptIntervalMs := by
  unfold State.nextTick
  simp only [h, ↓reduceIte]
  cases s.freshFlag <;> cases s.lastOutMs <;> simp [Nat.min_le_left]

/-- Fresh output gets its tick no later than the moment it stops being fresh. -/
theorem nextTick_stale (s : State) {t : Nat} (h : s.freshFlag = true) (ho : s.lastOutMs = some t) :
    ∃ due, s.nextTick = some due ∧ due ≤ t + freshMs := by
  unfold State.nextTick
  simp only [h, ho, ↓reduceIte, Option.map_some]
  cases s.dirty <;> simp [Nat.min_le_right]

/-- Output since the previous tick is fresh at this one, and schedules the tick that ends its
freshness. -/
theorem step_tick_fresh (s : State) (now : Nat) (hout : s.tickOutSeq < s.outSeq) :
    (step s (.tick now)).1.freshFlag = true ∧
      ∃ due, (step s (.tick now)).1.nextTick = some due ∧ due ≤ now + freshMs := by
  have hfresh :
    (step s (.tick now)).1.freshFlag = true ∧ (step s (.tick now)).1.lastOutMs = some now := by
    simp only [step]
    split <;> simp [State.ticked, hout, freshMs]
  exact ⟨hfresh.1, nextTick_stale _ hfresh.1 hfresh.2⟩

/-- **Idle is free**: a tick that finds nothing unsaved, no output since the previous tick and
the last output already stale leaves the session needing no tick, so its daemon sleeps until
the next event. -/
theorem step_tick_sleeps (s : State) (now : Nat) (hd : s.dirty = false)
    (hout : s.tickOutSeq = s.outSeq) (hstale : ∀ t, s.lastOutMs = some t → t + freshMs ≤ now) :
    (step s (.tick now)).1.nextTick = none := by
  have hlt : ¬s.tickOutSeq < s.outSeq := by omega
  rw [nextTick_eq_none]
  simp only [step, hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte, State.ticked, hlt]
  refine ⟨trivial, Or.inl ?_⟩
  cases ho : s.lastOutMs with
  | none => rfl
  | some t =>
    have := hstale t ho
    simp only [Option.any_some, decide_eq_false_iff_not]
    omega

/-- What a tick leaves of the reasons to tick again: it has seen all output so far, its unsaved
changes outlive it only while their save is not yet due, its output is fresh exactly while the
last output it knows of is younger than `freshMs`, and when it had seen all output already, the
last output it knows of is the one it knew. -/
theorem tick_facts (s : State) (now : Nat) :
    let s' := (step s (.tick now)).1
    s'.tickOutSeq = s'.outSeq ∧
      (s'.dirty = true →
        s.dirty = true ∧ now < s.lastCkptMs + ckptIntervalMs ∧ s'.lastCkptMs = s.lastCkptMs) ∧
      s'.freshFlag = s'.lastOutMs.any (now < · + freshMs) ∧
      (s.tickOutSeq = s.outSeq → s'.lastOutMs = s.lastOutMs) := by
  simp only [step, State.ticked]
  split <;> simp_all

/-- A session's next tick is the earlier of its save, while it has unsaved changes, and the end
of its output's freshness, while that output is fresh. -/
theorem nextTick_some (s : State) {t : Nat} (h : s.nextTick = some t) :
    (s.dirty = true → t ≤ s.lastCkptMs + ckptIntervalMs) ∧
      (∀ l, s.freshFlag = true → s.lastOutMs = some l → t ≤ l + freshMs) ∧
      (s.dirty = true ∧ t = s.lastCkptMs + ckptIntervalMs ∨
        ∃ l, s.freshFlag = true ∧ s.lastOutMs = some l ∧ t = l + freshMs) := by
  unfold State.nextTick at h
  cases hd : s.dirty <;> cases hf : s.freshFlag <;> cases hl : s.lastOutMs <;> simp_all
  all_goals omega

/-- **After the last event, a daemon wakes at most twice on its own.** Ticking at the deadlines
its session sets, for its save and for the end of its output's freshness, the session then needs
no tick until the next event. The tick that ends an event's poll round has seen all output, so
the last output stays the one it knows, the deadlines only move later, and each tick at the
earlier one settles its reason without reviving the other. -/
theorem ticks_settle (s : State) (now t₁ t₂ : Nat)
    (h₁ : (trace step s [.tick now]).1.nextTick = some t₁)
    (h₂ : (trace step s [.tick now, .tick t₁]).1.nextTick = some t₂) :
    (trace step s [.tick now, .tick t₁, .tick t₂]).1.nextTick = none := by
  simp only [trace] at h₁ h₂ ⊢
  obtain ⟨q0, d0, f0, -⟩ := tick_facts s now
  obtain ⟨q1, d1, f1, l1⟩ := tick_facts (step s (.tick now)).1 t₁
  obtain ⟨-, d2, f2, l2⟩ := tick_facts (step (step s (.tick now)).1 (.tick t₁)).1 t₂
  have n1 := nextTick_some _ h₁
  have n2 := nextTick_some _ h₂
  rw [nextTick_eq_none]
  generalize (step s (.tick now)).1 = s0 at *
  generalize (step s0 (.tick t₁)).1 = s1 at *
  generalize (step s1 (.tick t₂)).1 = s2 at *
  have l1 := l1 q0
  have l2 := l2 q1
  rw [l1] at l2
  rw [l1] at f1 n2
  rw [l2] at f2 ⊢
  clear h₁ h₂ q0 q1 l1 l2
  revert d0 d1 d2 f0 f1 f2 n1 n2
  cases s0.lastOutMs <;> cases s0.dirty <;> cases s1.dirty <;> cases s2.dirty <;>
    cases s0.freshFlag <;>
    cases s1.freshFlag <;>
    cases s2.freshFlag <;>
    simp <;>
    omega

theorem setClient_length (s : State) (c : Client) :
    (s.setClient c).clients.length = s.clients.length := by simp [State.setClient]

theorem dropClient_length_le (s : State) (id : Nat) :
    (s.dropClient id).clients.length ≤ s.clients.length := List.length_filter_le _ _

theorem closeClient_bounded (s : State) (id : Nat) (h : Bounded s) :
    Bounded (closeClient s id).1 := by
  unfold closeClient
  dsimp only
  split
  all_goals
    refine ⟨Nat.le_trans (dropClient_length_le s id) h.clientsLe, h.fieldsLe, ?_, h.scanOk⟩
    intro c hmem
    exact h.decOk c (List.mem_filter.mp hmem).1

/-- `onMsg` never grows the client list. -/
theorem onMsg_clients_length_le (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).1.clients.length ≤ s.clients.length := by
  unfold onMsg
  grind

/-- `onMsg` keeps the record fields within the cap. -/
theorem onMsg_fields_le (s : State) (c : Client) (m : Msg) (h : s.fields.length ≤ maxFields) :
    (onMsg s c m).1.fields.length ≤ maxFields := by
  unfold onMsg
  grind

/-- Rewriting one client (same decoder) keeps every stored decoder
healthy. -/
theorem decOk_setClient (s : State) (c0 : Client)
    (hc0 : c0.decoder.errored = false ∧ c0.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h :
      ∀ c' ∈ s.clients, c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload) :
    ∀ c' ∈ (s.setClient c0).clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload := by
  simp only [State.setClient, List.mem_map]
  grind

/-- `onMsg` preserves per-client decoder health: it only ever copies
existing decoders around (attach/resize/wait rewrite other fields). -/
theorem onMsg_decOk (s : State) (c : Client) (m : Msg)
    (hc : c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h :
      ∀ c' ∈ s.clients, c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload) :
    ∀ c' ∈ (onMsg s c m).1.clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload := by
  unfold onMsg controlResize resizeOwned resize
  dsimp only
  repeat' split
  all_goals
    first
    | exact h
    | exact decOk_setClient _ _ hc h
    | exact decOk_setClient _ _ hc (decOk_setClient _ _ hc h)

theorem onMsg_scan (s : State) (c : Client) (m : Msg) : (onMsg s c m).1.scan = s.scan := by
  unfold onMsg
  grind

/-- One message preserves the bound quadruple. -/
theorem onMsg_bounded {s : State} {c : Client} (m : Msg)
    (hc : c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload) (h : Bounded s) :
    Bounded (onMsg s c m).1 :=
  ⟨Nat.le_trans (onMsg_clients_length_le s c m) h.clientsLe, onMsg_fields_le s c m h.fieldsLe,
    onMsg_decOk s c m hc h.decOk, by
    rw [onMsg_scan]; exact h.scanOk⟩

theorem client?_mem {s : State} {id : Nat} {c : Client} (h : s.client? id = some c) :
    c ∈ s.clients := List.mem_of_find?_eq_some h

/-- Induct over the actual batch accumulator, including its effects. A handler
needs to preserve the predicate only for messages in this batch, after the stop
guards and sender lookup succeed. Skipped messages keep the entire accumulator. -/
theorem feedMsgs_induct (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    {P : State × List (Effect Plan) → Prop}
    (pres :
      ∀ acc c m,
        m ∈ msgs →
          Effect.close id ∉ acc.2 →
          Effect.exit ∉ acc.2 →
          acc.1.client? id = some c → P acc → P ((onMsg acc.1 c m).1, acc.2 ++ (onMsg acc.1 c m).2))
    (h : P acc) : P (feedMsgs id msgs acc) := by
  unfold feedMsgs
  apply List.foldlRecOn
  · exact h
  · intro current hc m hm
    split
    · exact hc
    · rename_i hstop
      simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at hstop
      split
      · exact hc
      · rename_i c hfind
        exact pres current c m hm hstop.1 hstop.2 hfind hc

/-- Batch boundaries preserve the exact state and ordered effects, including
pending stops. Splitting decoded messages never grants a sender new authority. -/
theorem feedMsgs_append (id : Nat) (before after : List Msg) (acc : State × List (Effect Plan)) :
    feedMsgs id (before ++ after) acc = feedMsgs id after (feedMsgs id before acc) :=
  List.foldl_append

/-- Once any prefix requests this sender's close or exit, every suffix is
inert: the result is exactly the prefix's state and effects. -/
theorem feedMsgs_stopped_suffix (id : Nat) (before after : List Msg)
    (acc : State × List (Effect Plan))
    (h : Effect.close id ∈ (feedMsgs id before acc).2 ∨ Effect.exit ∈ (feedMsgs id before acc).2) :
    feedMsgs id (before ++ after) acc = feedMsgs id before acc := by
  rw [feedMsgs_append]
  apply feedMsgs_induct id after (feedMsgs id before acc) (P := (· = feedMsgs id before acc)) ?_ rfl
  intro current _ _ _ hclose hexit _ heq
  subst current
  exact (h.elim hclose hexit).elim

/-- Once this sender has a close pending, no remaining decoded message changes
the state or adds an effect. Transport draining does not extend its authority. -/
theorem feedMsgs_after_close (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (h : Effect.close id ∈ acc.2) : feedMsgs id msgs acc = acc :=
  feedMsgs_stopped_suffix id [] msgs acc (Or.inl h)

/-- Exit stops every remaining decoded command, regardless of sender. -/
theorem feedMsgs_after_exit (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (h : Effect.exit ∈ acc.2) : feedMsgs id msgs acc = acc :=
  feedMsgs_stopped_suffix id [] msgs acc (Or.inr h)

/-- Lift a state invariant through the actual message batch. The lookup witness
lets each invariant use the sender's membership and identity when needed. -/
theorem feedMsgs_preserves (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    {P : State → Prop} (pres : ∀ s c m, s.client? id = some c → P s → P (onMsg s c m).1)
    (h : P acc.1) : P (feedMsgs id msgs acc).1 :=
  feedMsgs_induct id msgs acc (P := fun r => P r.1)
    (fun current c m _ _ _ hc hs => pres current.1 c m hc hs) h

/-- Any state invariant preserved by the supplied events holds after their
trace. Membership permits restricted alphabets, such as one client's bytes.
The runtime instance uses its consumed trace, ending at exit. -/
theorem run_preserves (s : State) (evs : List Event) {P : State → Prop}
    (pres : ∀ s ev, ev ∈ evs → P s → P (step s ev).1) (h : P s) : P (run s evs).1 := by
  induction evs generalizing s with
  | nil => exact h
  | cons ev evs ih =>
    exact
      ih (step s ev).1 (fun s e he hs => pres s e (List.mem_cons_of_mem ev he) hs)
        (pres s ev List.mem_cons_self h)

theorem feedMsgs_bounded (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (h : Bounded acc.1) : Bounded (feedMsgs id msgs acc).1 :=
  feedMsgs_preserves id msgs acc
    (fun _ _ m hc hs => onMsg_bounded m (hs.decOk _ (client?_mem hc)) hs) h

/-- The bounds at the daemon level: no event stream can grow the client
list, label table, client decoders, or terminal scanner past their caps. -/
theorem step_bounded (s : State) (ev : Event) (h : Bounded s) : Bounded (step s ev).1 := by
  obtain ⟨hcl, hlb, hdec, hscan⟩ := h
  have h' : Bounded s := ⟨hcl, hlb, hdec, hscan⟩
  unfold step
  split
  · -- connected
    split
    · exact h'
    · rename_i hlt
      refine ⟨?_, hlb, ?_, hscan⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro c' hmem
        rcases List.mem_append.mp hmem with hm | hm
        · exact hdec c' hm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          subst hm
          exact ⟨rfl, by simp [Wire.maxPayload]⟩
  · -- bytes
    rename_i id chunk
    split
    · exact h'
    · rename_i c hfind
      dsimp only
      split
      · -- decoder errored: client dropped
        exact closeClient_bounded s id h'
      · rename_i herr
        apply feedMsgs_bounded
        dsimp only
        have hcmem := client?_mem hfind
        have hcok := hdec c hcmem
        -- the new decoder is healthy: not errored (guard) and capped
        refine ⟨?_, hlb, ?_, hscan⟩
        · simpa [setClient_length] using hcl
        · refine decOk_setClient s _ ⟨?_, ?_⟩ hdec
          · dsimp only
            simpa using herr
          · dsimp only
            have := Wire.Decoder.feed_buf_le c.decoder chunk (by simp [hcok.1])
            rcases hsplit : c.decoder.feed chunk with ⟨d2, ms2⟩
            rw [hsplit] at this
            simpa [hsplit] using this
  · -- closed (may checkpoint; state shape identical either way)
    exact closeClient_bounded s _ h'
  · -- ptyOut
    exact ⟨hcl, hlb, hdec, Terminal.Mediation.feed_bounded _ _ _ hscan⟩
  · -- childExited: finish always returns ground
    exact ⟨hcl, hlb, hdec, Terminal.Mediation.finish_bounded s.scan⟩
  · -- stopped: the same ending
    exact ⟨hcl, hlb, hdec, Terminal.Mediation.finish_bounded s.scan⟩
  · -- signal: the same ending, after the stop
    exact ⟨hcl, hlb, hdec, Terminal.Mediation.finish_bounded s.scan⟩
  · -- tick
    split
    · exact ⟨hcl, hlb, hdec, hscan⟩
    · exact ⟨hcl, hlb, hdec, hscan⟩
  · -- an observation changes only what `info` reports
    exact ⟨hcl, hlb, hdec, hscan⟩
  · -- failed checkpoint changes only persistence bookkeeping
    exact ⟨hcl, hlb, hdec, hscan⟩

/-! ## VT preservation through the daemon -/

/-- Every message either retains the terminal or resizes it. Any predicate
closed under resize therefore survives, without restrictions on the message. -/
theorem onMsg_vt_preserves {P : Vt.Vt → Prop}
    (hresize : ∀ vt cols rows, P vt → P (vt.resize cols rows)) {s : State} {c : Client} (m : Msg)
    (h : P s.vt) : P (onMsg s c m).1.vt := by
  unfold onMsg
  grind

/-- Resize and feed are the only terminal transitions a session performs.
This lifts either kind of terminal invariant through the actual message batch
and mediator, retaining their stop behavior and VT projection. -/
theorem step_vt_preserves {P : Vt.Vt → Prop}
    (hresize : ∀ vt cols rows, P vt → P (vt.resize cols rows))
    (hfeed : ∀ vt bytes, P vt → P (vt.feed bytes)) (s : State) (ev : Event) (h : P s.vt) :
    P (step s ev).1.vt := by
  unfold step
  split
  · split
    · exact h
    · exact h
  · split
    · exact h
    · dsimp only
      split
      · simpa only [closeClient_vt] using h
      · apply
          feedMsgs_preserves _ _ _ (P := fun s => P s.vt)
            (fun _ _ m _ hs => onMsg_vt_preserves hresize m hs)
        simpa [State.setClient] using h
  · simpa only [closeClient_vt] using h
  · -- ptyOut
    dsimp only
    rw [Terminal.Mediation.feed_vt]
    exact hfeed _ _ h
  · exact h
  · exact h
  · exact h
  · split
    · exact h
    · exact h
  · exact h
  · exact h

open Terminal.Vt (Good) in
/-- End to end: the screen state a daemon holds stays Good
whatever events arrive — adversarial clients and pty output included. -/
theorem step_vt_good (s : State) (ev : Event) (h : Good s.vt) : Good (step s ev).1.vt :=
  step_vt_preserves (fun _ cols rows hv => Terminal.Vt.Good.resize cols rows hv)
    (fun _ bytes hv => Terminal.Vt.Good.feed bytes hv) s ev h

/-! ## The unread counter

`unseen` is "output arrived while nobody was watching", and it is a property
of the **session**: `lookSeq` catches up on attach, on every output that
happens while somebody is attached, and on a capture (`.screen` — a capture is
a look), so a one-off connection from a stranger creates
no per-client state. A counter rather than a timestamp because it is
determined by the event list alone.

Two layers here: the exact claims about the events that *write* the counters,
and — since `.screen` made the read mark a two-writer field and `behind` an
agent-facing API — the general honesty pair over any traffic: no client
message moves `outSeq` (`onMsg_outSeq`: activity cannot be forged), and the
read mark never overtakes the counter (`run_lookSeq_le`), so
`behind = outSeq - lookSeq` is a real count over the daemon's whole life,
never a Nat-subtraction lie.
-/

/-- Pty output advances the counter by exactly one. -/
theorem outSeq_ptyOut (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.outSeq = s.outSeq + 1 := rfl

/-- Output while somebody is attached is seen as it happens; output with
nobody attached is not. This is the whole mechanism behind `wantsYou`. -/
theorem unseen_ptyOut (s : State) (chunk : List UInt8) (h : s.lookSeq ≤ s.outSeq) :
    unseen (step s (.ptyOut chunk)).1 = !(s.clients.any (·.attached)) := by
  simp only [unseen, step]
  grind

/-- **A capture is a look.** The exact shape: the reply
is `Render.screenText` — the grid, never the ring — chunked and closed with
`.done`, and the ONLY state changes are the read mark catching up and the read's
answer being recorded. An exact equation, so any smuggled side effect (a vt
touch, a label change) breaks it. -/
theorem onMsg_screen (s : State) (c : Client) (ha : c.answered = false) :
    onMsg s c .screen =
      ({ s.setClient { c with answered := true } with
          lookSeq := s.outSeq, asking := false, notice := none, finished := none },
        outputMsgs c.id (Render.screenText s.vt) ++ [.send c.id .done]) := by
  simp [onMsg, ha]

/-- …so after a capture nothing is unseen: "output arrived while nobody was
watching" is false of a session whose screen was just delivered. `.info`
deliberately has no such effect (`ls` polls every daemon), and `.history`
stays an export — the line is drawn at verbs that show the current screen. -/
theorem screen_marks_seen (s : State) (c : Client) (ha : c.answered = false) :
    unseen (onMsg s c .screen).1 = false := by simp [onMsg_screen s c ha, unseen, State.setClient]

/-- …and `behind` counts from the capture: zero at the moment of the look, so
what an agent reads later really is "output events since I captured". -/
theorem screen_behind_zero (s : State) (c : Client) (ha : c.answered = false) :
    behind (onMsg s c .screen).1 = 0 := by simp [onMsg_screen s c ha, behind, State.setClient]

/-- **No client message moves the output counter.** `outSeq` advances only on
`.ptyOut` — real child output — so no connection, whatever it sends, can
forge activity: `unseen`, `fresh` and `behind` can be *caught up* by a look
(attach, capture) but never inflated by traffic. -/
theorem onMsg_outSeq (s : State) (c : Client) (m : Msg) : (onMsg s c m).1.outSeq = s.outSeq := by
  unfold onMsg
  grind

/-- The read mark never overtakes the counter through any message: every arm
leaves `lookSeq` alone or catches it up to `outSeq` (attach and capture — the
looks), and none touches `outSeq`. -/
theorem onMsg_lookSeq_le (s : State) (c : Client) (m : Msg) (h : s.lookSeq ≤ s.outSeq) :
    (onMsg s c m).1.lookSeq ≤ (onMsg s c m).1.outSeq := by
  unfold onMsg
  grind

theorem feedMsgs_lookSeq_le (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (h : acc.1.lookSeq ≤ acc.1.outSeq) :
    (feedMsgs id msgs acc).1.lookSeq ≤ (feedMsgs id msgs acc).1.outSeq :=
  feedMsgs_preserves id msgs acc (P := fun s => s.lookSeq ≤ s.outSeq)
    (fun _ _ _ _ hs => onMsg_lookSeq_le _ _ _ hs) h

/-- One event keeps `behind` honest, whatever it is. -/
theorem step_lookSeq_le (s : State) (ev : Event) (h : s.lookSeq ≤ s.outSeq) :
    (step s ev).1.lookSeq ≤ (step s ev).1.outSeq := by
  unfold step closeClient
  dsimp only
  repeat' split
  all_goals
    first
    | exact h
    | (apply feedMsgs_lookSeq_le; exact h)
    | (dsimp only; omega)

/-- **The unread counter over the daemon's whole life**: no event trace of any length —
adversarial clients, captures, attaches, hostile pty bytes, any interleaving —
makes the read mark overtake the output counter. `behind = outSeq - lookSeq`
is therefore a real count forever (a fresh daemon starts at `0 ≤ 0`), and the
agent loop "capture, then poll `behind`/`outseq`" rests on this rather than on
Nat subtraction clamping a lie to zero. -/
theorem run_lookSeq_le (s : State) (evs : List Event) (h : s.lookSeq ≤ s.outSeq) :
    (run s evs).1.lookSeq ≤ (run s evs).1.outSeq :=
  run_preserves s evs (P := fun s => s.lookSeq ≤ s.outSeq)
    (fun s ev _ hs => step_lookSeq_le s ev hs) h

/-! ## Isolation — one client cannot reach another client's state

The concurrency question, at the layer where it is answerable. The
daemon is single-threaded: `poll` reports several ready fds, the
runtime reads each into its own `.bytes` event, and `step` serializes
them — so there are no data races by construction. What remains is
*interleaving*, and the hazard is cross-talk: could bytes from client A
corrupt client B's frame boundaries, or rewrite B's record?

It cannot: `.bytes id` touches only client `id`'s record. Every
other client's decoder — mid-frame or not — is bit-identical
afterwards, whatever bytes arrive and however they were chunked (the wire's
re-chunking invariance, `Wire.Decoder.feed_append`, supplies the per-connection half: any
split of A's stream yields the same messages in the same order).
-/

theorem client?_id {s : State} {id : Nat} {c : Client} (h : s.client? id = some c) : c.id = id := by
  have hp := (List.find?_eq_some_iff_append.mp h).1
  simpa using hp

/-- Rewriting one element of a client list cannot change what a lookup
for a *different* id finds. -/
theorem find?_map_set (c : Client) (other : Nat) (hne : other ≠ c.id) :
    ∀ (l : List Client),
      (l.map (fun c' => if c'.id == c.id then c else c')).find? (·.id == other) =
        l.find? (·.id == other) := by
  intro l
  induction l <;> grind

/-- Dropping one client cannot change what a lookup for a different id
finds. -/
theorem find?_filter_drop (id other : Nat) (hne : other ≠ id) :
    ∀ (l : List Client),
      (l.filter (·.id != id)).find? (·.id == other) = l.find? (·.id == other) := by
  intro l
  rw [List.find?_filter]
  congr 1
  funext c
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, bne_iff_ne, beq_iff_eq]
  exact ⟨And.right, fun h => ⟨fun hid => hne (h.symm.trans hid), h⟩⟩

theorem setClient_other {s : State} {c : Client} {other : Nat} (h : other ≠ c.id) :
    (s.setClient c).client? other = s.client? other := find?_map_set c other h s.clients

theorem dropClient_other {s : State} {id other : Nat} (h : other ≠ id) :
    (s.dropClient id).client? other = s.client? other := find?_filter_drop id other h s.clients

/-- One message from `c` leaves every other client's record alone. -/
theorem onMsg_other (s : State) (c : Client) (m : Msg) {other : Nat} (h : other ≠ c.id) :
    (onMsg s c m).1.client? other = s.client? other := by
  have twice {c1 c2 : Client} (h1 : c1.id = c.id) (h2 : c2.id = c.id) :
    ((s.setClient c1).setClient c2).client? other = s.client? other := by
    rw [setClient_other (h2 ▸ h), setClient_other (h1 ▸ h)]
  unfold onMsg controlResize resizeOwned resize
  dsimp only
  repeat' split
  all_goals
    first
    | rfl
    | exact setClient_other h
    | exact twice rfl rfl

/-- …and so does a whole batch of them. -/
theorem feedMsgs_other (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan)) {other : Nat}
    (h : other ≠ id) : (feedMsgs id msgs acc).1.client? other = acc.1.client? other := by
  apply feedMsgs_preserves id msgs acc (P := fun s => s.client? other = acc.1.client? other) ?_ rfl
  intro s c m hc hs
  rw [onMsg_other s c m
      (by
        rw [client?_id hc]; exact h)]
  exact hs

/-- Isolation: bytes from one client cannot alter another client's
record — including its wire decoder, so a peer stuck mid-frame stays
mid-frame and resumes correctly on its next chunk. Daemon-level
concurrency safety is this, plus re-chunking invariance (per-connection ordering),
plus single-threadedness. -/
theorem step_bytes_isolates (s : State) (id : Nat) (chunk : List UInt8) {other : Nat}
    (h : other ≠ id) : (step s (.bytes id chunk)).1.client? other = s.client? other := by
  unfold step
  dsimp only
  split
  · rfl
  · rename_i c hfind
    split
    · dsimp only [closeClient]
      split <;> exact dropClient_other h
    · rw [feedMsgs_other id _ _ h]
      exact
        setClient_other
          (by
            rw [client?_id hfind]; exact h)

/-! ## Trace lift — the per-step theorems over the daemon's whole life

`run` folds the events actually consumed, including effect feedback; the runtime
pump chooses that trace and stops at exit. These theorems cover every such trace,
without asserting that queued events after exit are consumed. `run_preserves`
supplies the common induction; the exact fold law also pins state threading and
effect order.
-/

/-- `run` is exactly the effect-accumulating fold of `step` — state
threading and effect order both. Pins the definition: any deviation
(dropped effects, unthreaded state) breaks this. -/
theorem run_eq_foldl (s : State) (evs : List Event) :
    run s evs =
      evs.foldl
        (fun (acc : State × List (Effect Plan)) ev =>
          ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2))
        (s, []) := by
  have hfold :
    ∀ evs s fx,
      evs.foldl
          (fun (acc : State × List (Effect Plan)) ev =>
            ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2))
          (s, fx) =
        ((run s evs).1, fx ++ (run s evs).2) := by
    intro evs
    induction evs with
    | nil =>
      intros; simp [run]
    | cons ev evs ih =>
      intros; simp [run, List.foldl_cons, ih, List.append_assoc]
  simpa using (hfold evs s []).symm

/-- The daemon's composite invariant: everything the per-step theorems
preserve, as one predicate. -/
def WF (s : State) : Prop := Bounded s ∧ Terminal.Vt.Good s.vt

theorem step_wf (s : State) (ev : Event) (h : WF s) : WF (step s ev).1 :=
  ⟨step_bounded s ev h.1, step_vt_good s ev h.2⟩

/-- The bounds and the screen invariant over the daemon's whole life: no event trace of any
length — adversarial clients, hostile pty bytes, any interleaving — can
break the bounds or the screen invariant. -/
theorem run_wf (s : State) (evs : List Event) (h : WF s) : WF (run s evs).1 :=
  run_preserves s evs (fun s ev _ hs => step_wf s ev hs) h

/-- Isolation over a whole trace, as the headline of this name (`Challenge.lean`, part 2)
states it over `Session.trace`: one client's entire byte stream,
however chunked, leaves every other client's record — decoder included
— bit-identical. -/
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other := by
  apply run_preserves _ _ (P := fun t => t.client? other = s.client? other) ?_ rfl
  intro t ev hev ht
  obtain ⟨chunk, _, rfl⟩ := List.mem_map.mp hev
  rw [step_bytes_isolates t id chunk h]
  exact ht

/-! ## Renderability lifted to the daemon's whole life

The emulator-level invariant is only useful if the *daemon's* terminal satisfies
it, for any event trace. A session does exactly three things to its `Vt`: feeds
it pty bytes (through the mediator, whose VT projection is `Vt.feed` —
`Mediation.feed_vt`), resizes it on attach or resize, and nothing else. Those are
precisely `LiveReachableVt`'s constructors, so the lift is an induction with no
new content — which is the point: the replay theorem may assume a *reachable*
grid without that assumption smuggling in a side condition.
-/

open Terminal.Vt (Live LiveReachableVt Renderable)

/-- The daemon's terminal is one a live session can hold. -/
def LiveVt (s : State) : Prop := LiveReachableVt s.vt

/-- `LiveVt` holds exactly when the terminal the state shows is one a live session can hold. -/
theorem liveVt_iff (s : State) : LiveVt s ↔ LiveReachableVt s.terminal := Iff.rfl

/-- One event keeps the terminal reachable. -/
theorem step_vt_live (s : State) (ev : Event) (h : LiveVt s) : LiveVt (step s ev).1 :=
  step_vt_preserves (P := LiveReachableVt) (fun _ cols rows hv => hv.resize cols rows)
    (fun _ bytes hv => hv.feed bytes) s ev h

/-- …and so does a trace of any length. -/
theorem run_vt_live (s : State) (evs : List Event) (h : LiveVt s) : LiveVt (run s evs).1 :=
  run_preserves s evs (fun s ev _ hs => step_vt_live s ev hs) h

/-- **The shape hypothesis, discharged at the daemon level.** Whatever a session
has been through — adversarial clients, hostile pty bytes, resizes, any
interleaving — the grid it holds is one `Render.restore` can express. -/
theorem run_vt_renderable (s : State) (evs : List Event) (h : LiveVt s) :
    Renderable (run s evs).1.vt := Terminal.Vt.renderable_of_liveReachable (run_vt_live s evs h)

/-- A fresh boot through `State.boot`, the one door the runtime walks through,
satisfies the hypothesis, so the statement above is not conditional in practice. -/
theorem liveVt_boot (cols rows : Nat) (ls mk : List (String × String)) :
    LiveVt (State.boot (Vt.Vt.init cols rows) ls mk) := Live.init cols rows

/-! ## Resume at the daemon — the other door into `State.boot`

`liveVt_boot` covers a *fresh* boot. `Linger/Session/WorldCode/Daemon.lean` has a second
source for the `vt0` it boots with:

```
let vt0 := Linger.Session.bootVt (restore.map (·.1))
```

where `restore` is what the daemon recovered, as `Linger.App.Recovery.decide` answers from the
name's checkpoint file — `ck.vt` for a
`Checkpoint.loadBytes bytes = some ck`, which `Checkpoint.loadBytes_eq` turns into
`Checkpoint.load bytes.data.toList = some ck`. The decoder's `ofDecoded` rung says `LiveVt`
of that half (`Checkpoint.loadBytes_live`), and the claims below carry it through the
daemon's life. The shape to mirror is `boot_wf`/`run_boot_wf`
in the next section: a door lemma per source, one hypothesised whole-life claim, and
then the hypothesis-free form over the term the daemon actually computes. -/

/-- **The resume door.** A daemon booting from any byte string that loads at all holds a
state a live session can hold. `Checkpoint.load_live` is the whole content; what this adds
is that `State.boot` does not disturb it — the `take maxFields` `boot` performs touches the
labels, never the `Vt`. -/
theorem liveVt_boot_of_load {l : List UInt8} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.load l = some c) (ls mk : List (String × String)) :
    LiveVt (State.boot c.vt ls mk) := Checkpoint.load_live h

/-- **`Daemon.lean`'s `vt0`, as a pure function of the bytes on disk.** The runtime writes

```
let vt0 := Linger.Session.bootVt (restore.map (·.1))
```

with `restore` from the daemon's recovery (`Linger.App.Recovery.decide`), whose `some` case is
`(ck.vt, …)` for a `Checkpoint.loadBytes bytes = some ck`; it is `none` for a missing file when a
new session may start, bytes that do not decode (torn write, foreign tag, corrupt payload) start
nothing, and an existing file that cannot be read throws before the boot. So this is that
expression with the `IO` peeled off, and `b` ranges over every byte string that could be on
disk; for bytes that do not decode it is the fresh screen, though the daemon then boots none.

**Named rather than inlined**, for the reason `Vt.decodedOk` and `stripMagic` are named:
the two claims below repeat it six times between them and would be unreadable spelled out.
The daemon calls `bootVt` itself, so the model and the runtime share the fallback by
construction: `scripts/gates.sh` ties the daemon's call. -/
def resumeVt (b : ByteArray) : Vt.Vt := bootVt ((Checkpoint.loadBytes b).map (·.vt))

/-- **Both doors, in one step.** `bootVt`'s two branches are exactly the daemon's two
sources for `vt0`: `none` is a fresh `Vt.init 80 24`, `some` is a decoded checkpoint. This
is where the `ofDecoded` rung is load-bearing — the `some` branch has no other witness.
Stated over `bootVt` itself, the term `Daemon.lean` calls. -/
theorem liveReachableVt_resumeVt (b : ByteArray) :
    Terminal.Vt.LiveReachableVt (bootVt ((Checkpoint.loadBytes b).map (·.vt))) := by
  unfold bootVt
  rcases hl : Checkpoint.loadBytes b with - | c
  · exact Live.init 80 24
  · exact Checkpoint.loadBytes_live hl

/-- **A live terminal over the daemon's whole life, from either door.** The `LiveVt` analogue
of `run_boot_wf`: whatever a session has been through — adversarial clients, hostile pty
bytes, resizes, any interleaving — its terminal is still one a live session can hold,
whether it booted fresh (`liveVt_boot`) or resumed (`liveVt_boot_of_load`). -/
theorem run_boot_vt_live (vt : Vt.Vt) (labels metaKv : List (String × String)) (evs : List Event)
    (h : Terminal.Vt.LiveReachableVt vt) :
    LiveVt (run (State.boot vt labels metaKv) evs).1 := run_vt_live _ _ h

/-- **The screen's shape, made structural.** Every state the daemon can *possess*
— every state reachable from any boot, which by the `State` seal is all of them — has a
grid `Render.restore` can express and a tab ruler the width of it.

Stated as one theorem rather than as a chain for a reader to assemble: `run_vt_renderable`
needs `LiveVt s`, which for a decoded `vt0` comes from the resume door. `TabsOk` rides along
because it is the second hypothesis `Render.restore_tabs_any` and `Resume.resume_tabs` ask
for and `Renderable` does not carry. -/
theorem run_boot_vt_shape (vt : Vt.Vt) (labels metaKv : List (String × String)) (evs : List Event)
    (h : Terminal.Vt.LiveReachableVt vt) :
    Renderable (run (State.boot vt labels metaKv) evs).1.vt ∧
      Terminal.Vt.TabsOk (run (State.boot vt labels metaKv) evs).1.vt :=
  ⟨Terminal.Vt.renderable_of_liveReachable (run_boot_vt_live vt labels metaKv evs h),
    Terminal.Vt.tabsOk_of_liveReachable (run_boot_vt_live vt labels metaKv evs h)⟩

/-- **The same claim with no hypothesis at all, over the term the daemon computes.** `b` is
an arbitrary `ByteArray` — a corrupt file, a truncated one, a hostile one, or a real
checkpoint — and `resumeVt b` is `Daemon.lean`'s `vt0`. Both doors are the two branches of
`bootVt`, so this is the whole of "every screen the daemon can possess is one the emitter
can repaint, and every ruler is the width of its screen", quantified over every byte string
that could be on disk and every event trace.

The `some` branch rests on the `ofDecoded` rung, its only `LiveVt` witness. -/
theorem run_resume_vt_shape (b : ByteArray) (labels metaKv : List (String × String))
    (evs : List Event) :
    Renderable (run (State.boot (resumeVt b) labels metaKv) evs).1.vt ∧
      Terminal.Vt.TabsOk (run (State.boot (resumeVt b) labels metaKv) evs).1.vt :=
  run_boot_vt_shape _ labels metaKv evs (liveReachableVt_resumeVt b)

/-- **The checkpoint round trip across a *second* reboot.** The checkpoint a resumed session
writes loads back exactly, for any bytes it was resumed from and any trace it then ran.
`Checkpoint.load_save`'s three hypotheses are discharged in one step by the same reachability
(`Checkpoint.loadBytes_saveBytes_live`), which is the point: reboot-resume is idempotent
rather than one-shot.

The `.quiesce` on the right is content, not decoration — the round trip is exact *modulo*
the parser state a checkpoint deliberately forgets (`Checkpoint.wVt`). A poll boundary
can split an escape or UTF-8 sequence, so it does not establish parser quiescence. -/
theorem run_resume_load_save (b : ByteArray) (labels metaKv : List (String × String))
    (evs : List Event) (cwd : String) :
    Checkpoint.loadBytes
        (Checkpoint.saveBytes
          { vt := (run (State.boot (resumeVt b) labels metaKv) evs).1.vt, cwd,
            fields := (run (State.boot (resumeVt b) labels metaKv) evs).1.fields }) =
      some
        { vt := (run (State.boot (resumeVt b) labels metaKv) evs).1.vt.quiesce, cwd,
          fields := (run (State.boot (resumeVt b) labels metaKv) evs).1.fields } :=
  Checkpoint.loadBytes_saveBytes_live _
    (run_boot_vt_live _ labels metaKv evs (liveReachableVt_resumeVt b))

/-! ## The bounds at the door — boot is well-formed, so every daemon state is

With the constructor private, `State.boot` is the only
way a `State` comes to exist outside this module's friends, and `step` the
only way forward — so `boot_wf ∘ run_wf` stops being "the invariant holds if
the runtime starts politely" and covers every state the daemon can possess.
The labels conjunct is what `boot`'s `take` buys: without it, a corrupt
checkpoint's label list would boot straight past `maxFields` and `Bounded` would
be false of a resumed daemon. The `Good vt`
hypothesis is honest: a fresh boot has `Good (Vt.init …)`, and the resume
path's decoded emulator carries it from the checkpoint theorems' side. -/

theorem boot_wf (vt : Vt.Vt) (labels metaKv : List (String × String)) (h : Terminal.Vt.Good vt) :
    WF (State.boot vt labels metaKv) :=
  ⟨⟨Nat.zero_le _, List.length_take_le _ _, nofun, trivial⟩, h⟩

/-- **Well-formedness made structural**: every state reachable from any boot —
which, by the seal, is every state the daemon can possess — is well-formed,
whatever the trace: adversarial clients, hostile pty bytes, forged
checkpoints' label lists, any interleaving. -/
theorem run_boot_wf (vt : Vt.Vt) (labels metaKv : List (String × String)) (evs : List Event)
    (h : Terminal.Vt.Good vt) :
    WF (run (State.boot vt labels metaKv) evs).1 := run_wf _ _ (boot_wf vt labels metaKv h)

/-- **Only the size owner resizes the pty** — as a theorem rather than a
convention. `resizeOwned` emits a `resizePty` only for the client the size-ownership
cascade (`sizeOwner`: the newest attached writable client whose terminal has a size) actually
selected — a watcher or an older mirror never moves the pty out from under the active
user. -/
theorem resizeOwned_owner_only (s : State) (c : Client) :
    (resizeOwned s c).2 ≠ [] → (sizeOwner s).any (·.id == c.id) = true := by
  intro hne
  unfold resizeOwned at hne
  split at hne
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact h.2
  · exact (hne rfl).elim

/-- A resize emits at most one effect, using the resulting emulator dimensions. -/
theorem resize_snd_eq_nil_or (s : State) (cols rows : UInt32) :
    (resize s cols rows).2 = [] ∨
      (resize s cols rows).2 =
        [.resizePty (UInt32.ofNat (resize s cols rows).1.vt.colCount)
            (UInt32.ofNat (resize s cols rows).1.vt.rowCount)] := by
  unfold resize
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The conversion to the syscall's integer representation loses no geometry:
the effective dimensions are clamped before they become a pty effect. -/
theorem resize_agrees (s : State) (cols rows ec er : UInt32)
    (h : Effect.resizePty ec er ∈ (resize s cols rows).2) :
    ec.toNat = (resize s cols rows).1.vt.colCount ∧
      er.toNat = (resize s cols rows).1.vt.rowCount := by
  revert h
  unfold resize
  split
  · simp
  · intro h
    simp only [List.mem_singleton, Effect.resizePty.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    change
      (UInt32.ofNat (Vt.clampDim cols.toNat)).toNat = Vt.clampDim cols.toNat ∧
        (UInt32.ofNat (Vt.clampDim rows.toNat)).toNat = Vt.clampDim rows.toNat
    have hc := (Vt.clampDim_range cols.toNat).2.1
    have hr := (Vt.clampDim_range rows.toNat).2.1
    constructor <;> apply UInt32.toNat_ofNat_of_lt' <;> simp only [UInt32.size] <;> omega

/-- The actual message handler preserves the geometry correspondence on every
path; restoration bytes and replies cannot introduce another resize effect. -/
theorem onMsg_resizePty_agrees (s : State) (c : Client) (m : Msg) (ec er : UInt32)
    (h : Effect.resizePty ec er ∈ (onMsg s c m).2) :
    ec.toNat = (onMsg s c m).1.vt.colCount ∧ er.toNat = (onMsg s c m).1.vt.rowCount := by
  revert h
  unfold onMsg controlResize resizeOwned focusEffects
  dsimp only
  repeat' split
  all_goals intro h
  all_goals try simp [outputMsgs] at h
  all_goals exact resize_agrees _ _ _ _ _ h

/-- Equal effective dimensions preserve the entire state, including region,
tabs and the checkpoint's dirty bit. -/
theorem resize_same_effective (s : State) (cols rows : UInt32)
    (hsame :
      (s.vt.colCount == Vt.clampDim cols.toNat && s.vt.rowCount == Vt.clampDim rows.toNat) = true) :
    resize s cols rows = (s, []) := by simp only [resize, hsame, Bool.or_true, ite_true]

/-- Every actual geometry change schedules persistence, even in a quiet session. -/
theorem resize_changed_dirty (s : State) (cols rows : UInt32)
    (h : (resize s cols rows).1.vt ≠ s.vt) : (resize s cols rows).1.dirty = true := by
  unfold resize at *
  split <;> simp_all

/-- All successful label changes schedule persistence; rejected messages leave
the store alone and cannot satisfy the premise. -/
theorem onMsg_labels_changed_dirty (s : State) (c : Client) (m : Msg)
    (h : (onMsg s c m).1.fields ≠ s.fields) : (onMsg s c m).1.dirty = true := by
  unfold onMsg at *
  grind

/-! ## Size ownership — a control resize never overrides an attached client that sizes it

`linger resize` lets an agent size a *detached* session
so wrap is deterministic before a capture. The size-owner rule extends rather than
bends: an attached client that sizes the session always wins, and the refusal is loud — an
agent must not believe a size it never got. -/

/-- **The invariant.** While anybody attached owns the size, a control resize
changes nothing — not the emulator, not the pty — and says so. -/
theorem controlResize_never_overrides (s : State) (c : Client) (cols rows : UInt32)
    (h : (sizeOwner s).isSome = true) :
    controlResize s c cols rows =
      (s, [.send c.id (.err "an attached client owns the size".toUTF8.toList)]) := by
  unfold controlResize
  rw [ite_eq_left h]

/-- With nobody to fight, a genuine new size applies: exactly one `resizePty`
at the effective size, the emulator resized with it, then `.done`. -/
theorem controlResize_applies (s : State) (c : Client) (cols rows : UInt32)
    (hown : (sizeOwner s).isSome = false) (hnz : (cols == 0 || rows == 0) = false)
    (hdiff :
      ((s.vt.colCount == cols.toNat && s.vt.rowCount == rows.toNat) ||
          (s.vt.colCount == Vt.clampDim cols.toNat && s.vt.rowCount == Vt.clampDim rows.toNat)) =
        false) :
    controlResize s c cols rows =
      ({ s with
          vt := s.vt.resize cols.toNat rows.toNat, dirty := true },
        [.resizePty (UInt32.ofNat (s.vt.resize cols.toNat rows.toNat).colCount)
            (UInt32.ofNat (s.vt.resize cols.toNat rows.toNat).rowCount),
          .send c.id .done]) := by
  unfold controlResize
  rw [ite_eq_right (by simp [hown]), ite_eq_right (by simp [hnz])]
  simp only [resize, hdiff, Bool.false_eq_true, ite_false]
  rfl

/-- The same-size branch is inert on purpose: the emulator — scroll region and
tab ruler included — is untouched (`Vt.resize` would wipe both and no SIGWINCH
re-establishes them at an unchanged winsize; the attach guard's reason), and
the reply is still `.done`: idempotent success, the pty already IS that size. -/
theorem controlResize_same_size (s : State) (c : Client) (cols rows : UInt32)
    (hown : (sizeOwner s).isSome = false) (hnz : (cols == 0 || rows == 0) = false)
    (hsame : (s.vt.colCount == cols.toNat && s.vt.rowCount == rows.toNat) = true) :
    controlResize s c cols rows = (s, [.send c.id .done]) := by
  unfold controlResize
  rw [ite_eq_right (by simp [hown]), ite_eq_right (by simp [hnz])]
  simp only [resize, hsame, Bool.true_or, ite_true]
  rfl

/-- The `.resize` arm routes a non-attached connection's first request of a read
to the stage above (after recording the size and the answer on the client
record), so the three claims are about what the daemon actually runs. -/
theorem onMsg_resize_control (s : State) (c : Client) (cols rows : UInt32) (hc : c.attached = false)
    (ha : c.answered = false) :
    onMsg s c (.resize cols rows) =
      controlResize
        ((s.setClient
              { c with
                cols, rows }).setClient
          { c with
            cols, rows, answered := true })
        { c with
          cols, rows, answered := true }
        cols rows := by
  unfold onMsg
  simp [hc, ha]

/-- A later control resize from the same read is refused: no resize, no `done`. -/
theorem onMsg_resize_answered (s : State) (c : Client) (cols rows : UInt32)
    (hc : c.attached = false) (ha : c.answered = true) :
    onMsg s c (.resize cols rows) =
      (s.setClient
          { c with
            cols, rows },
        [.send c.id (.err "one request per read".toUTF8.toList)]) := by
  unfold onMsg
  simp [hc, ha]

/-- **Every control resize answers the requester** — `.done` or `.err`, never
silence. The three shape theorems above each show a reply *under their guard*;
this is the guard-free totality that makes the reply a contract: the branches
are exhaustive, so a future branch that silently drops (the attached path's
`(s, [])` shape) cannot appear here without failing this. It is the pure half
of the no-hang story — `Client.drainReplies` with `Client.replySilenceMs` owns
the other half, against daemons that predate the verb entirely. -/
theorem controlResize_replies (s : State) (c : Client) (cols rows : UInt32) :
    (controlResize s c cols rows).2.any
        (fun e =>
          match e with
          | .send i .done => i == c.id
          | .send i (.err _) => i == c.id
          | _ => false) =
      true := by
  unfold controlResize resize
  repeat' split
  all_goals simp

/-! ## One expensive reply per read

A read can decode thousands of requests, and each `info`, `history`, `screen` or control
`resize` answer costs a whole rendering or a whole resize. `onMsg_answered` and
`onMsg_resize_answered` refuse such a request once the read has answered one; below, that
guard is followed through a whole `.bytes` event, so the bound is on what the read emits. -/

/-- The requests a read answers at most once: `info`, `history`, `screen`, and `resize`
from a connection that is not attached. -/
def costly (c : Client) : Msg → Bool
  | .info | .history | .screen => true
  | .resize _ _ => !c.attached
  | _ => false

theorem find?_map_set_self (c : Client) :
    ∀ (l : List Client),
      (l.find? (·.id == c.id)).isSome →
        (l.map (fun c' => if c'.id == c.id then c else c')).find? (·.id == c.id) = some c := by
  intro l
  induction l <;> grind

/-- Rewriting a client's record makes it the record its id finds. -/
theorem client?_setClient {s : State} {c c0 : Client} (h : s.client? c.id = some c0) :
    (s.setClient c).client? c.id = some c := by
  unfold State.client? at h
  exact find?_map_set_self c s.clients (by simp [h])

theorem resize_clients (s : State) (cols rows : UInt32) :
    (resize s cols rows).1.clients = s.clients := by
  unfold resize; split <;> rfl

/-! ### Focus follows typing -/

/-- A resize by the size owner changes the terminal's geometry, never the roster or the modes
the program set. -/
theorem resizeOwned_frame (s : State) (c : Client) :
    (resizeOwned s c).1.clients = s.clients ∧ (resizeOwned s c).1.vt.getModes = s.vt.getModes := by
  unfold resizeOwned resize
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- Attaching a record that can type, under an identifier the roster holds, focuses the session. -/
theorem focused_setClient {s : State} {c c0 : Client} (h : s.client? c.id = some c0)
    (ha : c.attached = true) (hs : c.mode = .writable) : (s.setClient c).focused = true := by
  have h1 := client?_setClient (c := c) h
  unfold State.client? at h1
  simp only [State.focused, List.any_eq_true]
  exact ⟨c, List.mem_of_find?_eq_some h1, by simp [ha, hs]⟩

/-- **Focus follows typing**: when a writable client attaches to a session nobody could type
into, whatever its terminal's size, a program that enabled focus reporting hears that it gained
focus. -/
theorem onMsg_attach_focus (s : State) (c : Client) (cols rows : UInt32)
    (hc : s.client? c.id = some c) (h : c.attached = false) (hunfocused : s.focused = false)
    (hmode : s.vt.getModes.focusEvents = true) :
    Effect.writePty (focusReport true) ∈ (onMsg s c (.attach .writable cols rows)).2 := by
  let c' : Client :=
    { c with
      attached := true, mode := .writable, seq := s.attachSeq, cols, rows }
  let s1 : State :=
    { s.setClient c' with
      attachSeq := s.attachSeq + 1, lookSeq := s.outSeq, asking := false, notice := none,
      finished := none }
  have hfocused : (resizeOwned s1 c').1.focused = true := by
    have hf : s1.focused = true := focused_setClient (c := c') hc rfl rfl
    simp only [State.focused, (resizeOwned_frame s1 c').1]
    exact hf
  have hmodes : (resizeOwned s1 c').1.vt.getModes = s.vt.getModes := (resizeOwned_frame s1 c').2
  have key :
    focusEffects (Mode.writable == .writable) s.focused (resizeOwned s1 c').1 =
      [.writePty (focusReport true)] := by
    simp only [focusEffects, hunfocused, hfocused, hmodes, hmode]
    rfl
  unfold onMsg
  dsimp only
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  show
    Effect.writePty (focusReport true) ∈
      (resizeOwned s1 c').2 ++
        focusEffects (Mode.writable == .writable) s.focused (resizeOwned s1 c').1 ++
        _ ++
        _
  rw [key]
  simp

/-- …and when the last client that could type leaves, the program hears that it lost focus. -/
theorem closeClient_focus (s : State) (id : Nat) {c : Client} (hc : s.client? id = some c)
    (hs : c.mode = .writable) (hfocused : s.focused = true)
    (hlast : (s.dropClient id).focused = false) (hmode : s.vt.getModes.focusEvents = true) :
    Effect.writePty (focusReport false) ∈ (closeClient s id).2 := by
  have key :
    focusEffects ((s.client? id).any (·.mode == .writable)) s.focused (s.dropClient id) =
      [.writePty (focusReport false)] := by
    have hm : (s.dropClient id).vt.getModes.focusEvents = true := hmode
    simp only [focusEffects, hc, Option.any_some, hs, beq_self_eq_true, hfocused, hlast, hm]
    rfl
  unfold closeClient
  dsimp only
  rw [key]
  split <;> simp

/-- A program that did not enable focus reporting never hears a focus report, whoever attaches
or leaves. -/
theorem focusEffects_off (typist before : Bool) (s : State)
    (h : s.vt.getModes.focusEvents = false) : focusEffects typist before s = [] := by
  unfold focusEffects
  rw [h]
  simp

/-- The sender's record after one message: answered once a costly request is, and never
detached by it. -/
theorem onMsg_sender (s : State) (c : Client) (m : Msg) (hc : s.client? c.id = some c) :
    ∃ c',
      (onMsg s c m).1.client? c.id = some c' ∧
        c'.answered = (c.answered || costly c m) ∧
        (c'.attached = false →
          c.attached = false ∧ ∀ mode cols rows, m ≠ .attach mode cols rows) := by
  cases m with
  | attach mode cols rows =>
    unfold onMsg
    dsimp only
    split
    · rename_i ha
      exact ⟨c, hc, by simp [costly], by simp [ha]⟩
    · let c' : Client :=
        { c with
          attached := true, mode, seq := s.attachSeq, cols, rows }
      have h1 : (s.setClient c').client? c.id = some c' := client?_setClient (c := c') hc
      refine ⟨c', ?_, by simp [c', costly], by simp [c']⟩
      unfold resizeOwned
      split
      · simp only [State.client?, resize_clients]; exact h1
      · exact h1
  | resize cols rows =>
    unfold onMsg
    dsimp only
    let c1 : Client :=
      { c with
        cols, rows }
    let c2 : Client := { c1 with answered := true }
    have h1 : (s.setClient c1).client? c.id = some c1 := client?_setClient (c := c1) hc
    have h2 : ((s.setClient c1).setClient c2).client? c.id = some c2 :=
      client?_setClient (c := c2) h1
    split
    · rename_i ha
      refine ⟨c1, ?_, by simp [c1, costly, ha], by simp [c1, ha]⟩
      unfold resizeOwned
      split
      · simp only [State.client?, resize_clients]; exact h1
      · exact h1
    · rename_i ha
      split
      · rename_i hn
        exact ⟨c1, h1, by simp [c1, costly, hn], fun _ => ⟨by simpa using ha, by simp⟩⟩
      · refine ⟨c2, ?_, by simp [c2, costly, ha], fun _ => ⟨by simpa using ha, by simp⟩⟩
        unfold controlResize
        split
        · exact h2
        · split
          · exact h2
          · simp only [State.client?, resize_clients]; exact h2
  | info
  | history
  | screen =>
    have h1 := client?_setClient (c := { c with answered := true }) hc
    unfold onMsg
    dsimp only
    split
    · rename_i hn
      exact ⟨c, hc, by simp [costly, hn], fun h => ⟨h, by simp⟩⟩
    · refine ⟨{ c with answered := true }, ?_, by simp [costly], fun h => ⟨h, by simp⟩⟩
      simp only [State.client?] at h1 ⊢
      exact h1
  | wait =>
    unfold onMsg
    dsimp only
    split
    · exact ⟨c, hc, by simp [costly], fun h => ⟨h, by simp⟩⟩
    · exact
        ⟨{ c with waiting := true }, client?_setClient (c := { c with waiting := true }) hc, by
          simp [costly], fun h => ⟨h, by simp⟩⟩
  | _ =>
    refine ⟨c, ?_, by simp [costly], fun h => ⟨h, by simp⟩⟩
    unfold onMsg
    dsimp only
    repeat' split
    all_goals exact hc

/-- Outside the read's costly answer, a message sends no rendered frame. -/
theorem onMsg_unrendered (s : State) (c : Client) (m : Msg)
    (h : c.answered = true ∨ costly c m = false) : (onMsg s c m).2.all (!·.rendered) := by
  cases m <;> simp only [costly, or_true] at h
  all_goals
    unfold onMsg resizeOwned resize controlResize focusEffects
    dsimp only
    repeat' split
  all_goals simp_all [Effect.rendered]
  all_goals
    intro m told
    rcases told_mem told with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- …and, from a connection that is neither attached nor attaching, no pty resize. -/
theorem onMsg_unresized (s : State) (c : Client) (m : Msg)
    (h : c.answered = true ∨ costly c m = false) (ha : c.attached = false)
    (hm : ∀ mode cols rows, m ≠ .attach mode cols rows) : (onMsg s c m).2.all (!·.resizes) := by
  cases m
  case attach mode cols rows => exact absurd rfl (hm mode cols rows)
  all_goals
    simp only [costly, ha, or_true] at h
    unfold onMsg resizeOwned resize controlResize focusEffects
    dsimp only
    repeat' split
  all_goals simp_all [Effect.resizes]

/-- Effects a read has emitted before answering a costly request: no rendered frame, and
no pty resize while the sender is unattached. -/
def Unanswered (c : Client) (effs : List (Effect Plan)) : Prop :=
  effs.all (!·.rendered) = true ∧ (c.attached = false → effs.all (!·.resizes) = true)

/-- Effects around the read's one costly answer: the whole answer to one of the batch's
messages `msgs`, given to the sender's record `c'` in a state `t`. -/
def AnsweredOnce (id : Nat) (msgs : List Msg) (c : Client) (effs : List (Effect Plan)) : Prop :=
  ∃ pre post t c' m,
    m ∈ msgs ∧
      t.client? id = some c' ∧
      effs = pre ++ (onMsg t c' m).2 ++ post ∧
      (pre ++ post).all (!·.rendered) ∧ (c.attached = false → (pre ++ post).all (!·.resizes))

/-- A batch keeps the sender's record and its effects in one of the two shapes above. -/
theorem feedMsgs_one_reply (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (h :
      ∃ c,
        acc.1.client? id = some c ∧
          (c.answered = false → Unanswered c acc.2) ∧
          (c.answered = true → AnsweredOnce id msgs c acc.2)) :
    ∃ c,
      (feedMsgs id msgs acc).1.client? id = some c ∧
        (c.answered = false → Unanswered c (feedMsgs id msgs acc).2) ∧
        (c.answered = true → AnsweredOnce id msgs c (feedMsgs id msgs acc).2) := by
  refine
    feedMsgs_induct id msgs acc (P := fun acc =>
      ∃ c,
        acc.1.client? id = some c ∧
          (c.answered = false → Unanswered c acc.2) ∧
          (c.answered = true → AnsweredOnce id msgs c acc.2))
      ?_ h
  intro acc c0 m hm _ _ hc0 ⟨c, hc, hnone, hone⟩
  have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
  subst hcc
  have hid := client?_id hc
  obtain ⟨c', hc', hans, hatt⟩ := onMsg_sender acc.1 c0 m (hid ▸ hc)
  have hfr := onMsg_unrendered acc.1 c0 m
  have hrs := onMsg_unresized acc.1 c0 m
  refine ⟨c', hid ▸ hc', ?_, ?_⟩
  · intro hn
    have h0 : (c0.answered || costly c0 m) = false := hans ▸ hn
    simp only [Bool.or_eq_false_iff] at h0
    obtain ⟨hf, hr⟩ := hnone h0.1
    refine ⟨by simp [hf, hfr (Or.inr h0.2)], fun ha => ?_⟩
    obtain ⟨ha0, hm⟩ := hatt ha
    simp [hr ha0, hrs (Or.inr h0.2) ha0 hm]
  · intro _
    cases ha0 : c0.answered
    · -- this message is the read's costly answer
      obtain ⟨hf, hr⟩ := hnone ha0
      refine ⟨acc.2, [], acc.1, c0, m, hm, hc0, by simp, by simpa using hf, fun ha => ?_⟩
      simpa using hr (hatt ha).1
    · obtain ⟨pre, post, t, c1, m1, hm1, ht1, he, hf, hr⟩ := hone ha0
      refine
        ⟨pre, post ++ (onMsg acc.1 c0 m).2, t, c1, m1, hm1, ht1, by simp [he], ?_, fun ha => ?_⟩
      · simp only [List.all_append, Bool.and_eq_true] at hf ⊢
        exact ⟨hf.1, hf.2, hfr (Or.inl ha0)⟩
      · obtain ⟨ha1, hm⟩ := hatt ha
        have := hr ha1
        simp only [List.all_append, Bool.and_eq_true] at this ⊢
        exact ⟨this.1, this.2, hrs (Or.inl ha0) ha1 hm⟩

/-- **One expensive reply per read.** Every rendered frame one `.bytes` event emits, and
every pty resize when the connection is still unattached afterwards, lies in one answer
`onMsg t c' m`, where `m` is a message the read decoded and `c'` is the sender's record
in `t`; without such an answer the read emits none of them. So one read builds at most
one info answer, history or screen capture, or control resize, however many requests it
decodes; the rest are refused (`onMsg_answered`, `onMsg_resize_answered`). An attached
client's resizes follow its terminal and are outside this bound, and an attach replays
once per connection (`onMsg_attach_already`). -/
theorem step_bytes_one_reply (s : State) (id : Nat) (chunk : List UInt8) :
    ∃ pre ans post,
      (step s (.bytes id chunk)).2 = pre ++ ans ++ post ∧
        (ans = [] ∨
          ∃ c t c' m,
            s.client? id = some c ∧
              m ∈ (c.decoder.feed chunk).2 ∧ t.client? id = some c' ∧ ans = (onMsg t c' m).2) ∧
        (pre ++ post).all (!·.rendered) ∧
        (((step s (.bytes id chunk)).1.client? id).all (!·.attached) →
          (pre ++ post).all (!·.resizes)) := by
  -- with nothing costly, the effects surround an empty answer
  have quiet (R : List (Effect Plan) → Prop) (P : Prop) (effs : List (Effect Plan))
    (hf : effs.all (!·.rendered)) (hr : P → effs.all (!·.resizes)) :
    ∃ pre ans post,
      effs = pre ++ ans ++ post ∧
        (ans = [] ∨ R ans) ∧
        (pre ++ post).all (!·.rendered) ∧ (P → (pre ++ post).all (!·.resizes)) :=
    ⟨effs, [], [], by simp, Or.inl rfl, by simpa using hf, by simpa using hr⟩
  -- a batch that starts unanswered, with nothing emitted yet
  have fresh (msgs : List Msg) (t : State) (c : Client) (hc : t.client? id = some c)
    (ha : c.answered = false) :
    ∃ pre ans post,
      (feedMsgs id msgs (t, [])).2 = pre ++ ans ++ post ∧
        (ans = [] ∨ ∃ t' c' m, m ∈ msgs ∧ t'.client? id = some c' ∧ ans = (onMsg t' c' m).2) ∧
        (pre ++ post).all (!·.rendered) ∧
        (((feedMsgs id msgs (t, [])).1.client? id).all (!·.attached) →
          (pre ++ post).all (!·.resizes)) := by
    obtain ⟨cf, hcf, hnone, hone⟩ :=
      feedMsgs_one_reply id msgs (t, [])
        ⟨c, hc, fun _ => ⟨rfl, fun _ => rfl⟩, fun h => absurd (h.symm.trans ha) (by simp)⟩
    rw [hcf]
    simp only [Option.all_some, Bool.not_eq_eq_eq_not, Bool.not_true]
    cases hb : cf.answered
    · obtain ⟨hf, hr⟩ := hnone hb
      exact quiet _ _ _ hf hr
    · obtain ⟨pre, post, t', c', m, hm, ht, he, hf, hr⟩ := hone hb
      exact ⟨pre, _, post, he, Or.inr ⟨t', c', m, hm, ht, rfl⟩, hf, hr⟩
  unfold step
  dsimp only
  split
  · exact quiet _ _ [] rfl (fun _ => rfl)
  · rename_i c hfind
    split
    · have hcl := closeClient_effects s id
      have hall (p : Effect Plan → Bool) (hp : p (.close id) = false) (hq : p .checkpoint = false)
        (hw : p (.writePty (focusReport false)) = false) :
        (Effect.close id :: (closeClient s id).2).all (!p ·) := by
        simp only [List.all_cons, hp, Bool.not_false, Bool.true_and, List.all_eq_true]
        intro e he
        rcases hcl e he with rfl | rfl
        · rw [hq]
          rfl
        · rw [hw]
          rfl
      exact
        quiet _ _ (.close id :: (closeClient s id).2) (hall _ rfl rfl rfl)
          (fun _ => hall _ rfl rfl rfl)
    · have hid := client?_id hfind
      have h1 (c1 : Client) (he : c1.id = id) : (s.setClient c1).client? id = some c1 := by
        rw [← he]; exact client?_setClient (he ▸ hfind)
      obtain ⟨pre, ans, post, he, hans, hf, hr⟩ :=
        fresh _ _
          { c with
            decoder := (c.decoder.feed chunk).1, answered := false }
          (h1 _ hid) rfl
      refine ⟨pre, ans, post, he, ?_, hf, hr⟩
      rcases hans with h | ⟨t, c', m, hm, ht, ha⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, t, c', m, hfind, hm, ht, ha⟩

/-! ## Listing integrity — a listing record cannot be forged

`Status.name_clean` proves the *status* column carries neither framing byte, which is
what lets the porcelain be tab-separated with no escaping pass. This is the same
promise for every **other** column.

`.labelSet` applies no filter and `linger set` passes a value through, so a label value
containing a newline, as `linger set s x=$'a\nstatus\tlive'` sets, would otherwise forge an
extra record: a `status`/`state` pair in the listing that `Status.classify`'s consumers would
read as the session's state. The guard is at the **emit site**, which is why the claims
below need no hypothesis about where a field came from.

`infoText` builds `List UInt8` directly, which is what makes them provable at all: a
`String` does not reduce in the kernel — the argument
`packages/terminal/Terminal/CoreCode/Render.lean`'s header makes, and the reason `Render.history`'s
`rowText` is built on `List UInt8`, which earns it `history_framing`/`history_lines`.
`Verify/Coverage.lean` classifies emitted streams. -/

/-- Scrubbed glyph bytes are ≥ 0x20, so neither framing byte can come out of a key or
a value. `Render.utf8s` maps a C0 control — tab and newline included — to U+FFFD. -/
theorem utf8s_no_frame (cs : List Char) : ∀ b ∈ Render.utf8s cs, b ≠ 0x09 ∧ b ≠ 0x0A := by
  intro b hb
  obtain ⟨hge, -⟩ := Render.utf8s_no_ctl cs b hb
  exact
    ⟨fun he => by
      rw [he] at hge; exact absurd hge (by decide), fun he => by
      rw [he] at hge; exact absurd hge (by decide)⟩

/-- **Every byte of a listing is a framing byte or printable content.** -/
theorem infoText_framing (s : State) :
    ∀ b ∈ infoText s, b = 0x09 ∨ b = 0x0A ∨ (0x20 ≤ b ∧ b ≠ 0x7F) := by
  intro b hb
  simp only [infoText, List.mem_flatMap, List.mem_append, List.mem_singleton] at hb
  grind [Render.utf8s_no_ctl]

/-- **`info` text, character by character**: every reply byte belongs to the UTF-8 encoding
of a field separator, a record terminator or a codepoint that is no C0 control, DEL or C1
control. `infoText_framing` is the byte-level half, which an encoded C1 control satisfies. -/
theorem infoText_text (s : State) :
    ∃ cs : List Char,
      infoText s = cs.flatMap Render.utf8 ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  refine
    ⟨(infoFields s).flatMap fun (k, v) =>
        (k.toList.map Render.textChar).map Render.safeChar ++ ['\t'] ++
          (v.toList.map Render.textChar).map Render.safeChar ++
          ['\n'],
      ?_, ?_⟩
  · simp only [infoText, Render.utf8s_eq_flatMap, List.flatMap_assoc, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  · intro c hc
    obtain ⟨⟨k, v⟩, -, hmem⟩ := List.mem_flatMap.mp hc
    have safe (d : Char) :
      Render.safeChar (Render.textChar d) = Render.textChar d ∧
        (0x20 ≤ (Render.textChar d).toNat ∧
          (Render.textChar d).toNat ≠ 0x7F ∧
          ¬(0x80 ≤ (Render.textChar d).toNat ∧ (Render.textChar d).toNat < 0xA0)) :=
      ⟨Render.safeChar_eq_self (Render.textChar_safe d).1 (Render.textChar_safe d).2.1,
        Render.textChar_safe d⟩
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hmem
    rcases hmem with ((⟨e, ⟨d, -, rfl⟩, rfl⟩ | rfl) | ⟨e, ⟨d, -, rfl⟩, rfl⟩) | rfl
    · rw [(safe d).1]; exact Or.inr (Or.inr (safe d).2)
    · exact Or.inl rfl
    · rw [(safe d).1]; exact Or.inr (Or.inr (safe d).2)
    · exact Or.inr (Or.inl rfl)

theorem count_utf8s_frame (cs : List Char) (b : UInt8) (hb : b = 0x09 ∨ b = 0x0A) :
    (Render.utf8s cs).count b = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  obtain ⟨h9, h10⟩ := utf8s_no_frame cs b hmem
  rcases hb with h | h
  · exact h9 h
  · exact h10 h

theorem count_frame :
    ∀ (l : List (String × String)) (b : UInt8),
      b = 0x09 ∨ b = 0x0A →
        (l.flatMap
                (fun kv =>
                  Render.utf8s (kv.1.toList.map Render.textChar) ++ [0x09] ++
                    Render.utf8s (kv.2.toList.map Render.textChar) ++
                    [0x0A])).count
            b =
          l.length
  | [], _, _ => rfl
  | kv :: t, b, hb => by
    have hz : ∀ cs : List Char, (Render.utf8s cs).count b = 0 := fun cs => count_utf8s_frame cs b hb
    rw [List.flatMap_cons, List.count_append, count_frame t b hb]
    simp only [List.count_append, hz]
    rcases hb with h | h <;> subst h <;> simp <;> omega

/-- **One record per field, structurally.** As many newlines as fields and as many tabs
as fields — so a field *cannot* forge a record, however it was set. This is the
anti-forgery claim: an injected newline would make the newline count exceed the field
count, and `Remote.parseRecord` reads one record per line. -/
theorem infoText_records (s : State) :
    (infoText s).count 0x0A = (infoFields s).length ∧
      (infoText s).count 0x09 = (infoFields s).length := by
  unfold infoText
  exact ⟨count_frame (infoFields s) 0x0A (Or.inr rfl), count_frame (infoFields s) 0x09 (Or.inl rfl)⟩

/-! ## Chunking at the session layer — what a client receives is what was sent

The wire's round trip composed with re-chunking invariance (`decode_encode_chunked`) says the
*transport* is invisible:
any re-chunking of an encoded stream decodes to exactly that stream. The session does its own
framing on top of that — `outputMsgs` splits a payload into ≤ 64 KiB `output` frames, with
`chunksOf`.

Two claims, and they are the two properties the runtime depends on: the split loses
nothing (so program output, a capture and a history export arrive whole) and no frame exceeds
the cap (so `Msg.WF` holds of what the daemon actually sends). -/

theorem chunksOf_flatten {α : Type} (n : Nat) (l : List α) : (chunksOf n l).flatten = l := by
  induction l using chunksOf.induct n with
  | case1 l h =>
    rw [chunksOf]; simp [h]
  | case2 l h ih =>
    rw [chunksOf]; simp [h, ih, List.take_append_drop]

theorem chunksOf_le {α : Type} (n : Nat) (hn : 0 < n) (l : List α) :
    ∀ c ∈ chunksOf n l, c.length ≤ n := by
  induction l using chunksOf.induct n with
  | case1 l h =>
    rw [chunksOf]
    simpa [h] using (h.resolve_right (by omega) : l.length ≤ n)
  | case2 l h ih =>
    rw [chunksOf]
    simp only [h, ↓reduceDIte, List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · simpa only [List.length_take] using Nat.min_le_left n l.length
    · exact ih c hc

/-- Cutting a nonempty list gives no empty piece. -/
theorem chunksOf_ne_nil {α : Type} (n : Nat) (l : List α) (hl : l ≠ []) :
    ∀ c ∈ chunksOf n l, c ≠ [] := by
  induction l using chunksOf.induct n with
  | case1 l h =>
    rw [chunksOf]
    simpa [h] using hl
  | case2 l h ih =>
    rw [chunksOf]
    simp only [h, ↓reduceDIte, List.mem_cons]
    have hlen : n < l.length := by omega
    intro c hc
    rcases hc with rfl | hc
    · simp only [ne_eq, List.take_eq_nil_iff, not_or]
      exact ⟨by omega, hl⟩
    · have hrest : l.drop n ≠ [] := by
        simp only [ne_eq, List.drop_eq_nil_iff]
        omega
      exact ih hrest c hc

/-- The payloads of the frames `outputMsgs` produces are exactly its chunks.

Factored out because *both* claims below have to be stated about `outputMsgs` rather
than about `chunksOf`, and the break-verify is what showed why: a bound stated on
`chunksOf outputChunk bs` does not notice `outputMsgs` changing its chunk size —
doubling it left such a claim green. That is the difference between a claim about the
code and a claim sitting next to it. -/
theorem outputMsgs_payloads (id : Nat) (bs : List UInt8) :
    (outputMsgs id bs).filterMap
        (fun e =>
          match e with
          | .send _ (.output c) => some c
          | _ => none) =
      chunksOf outputChunk bs := by
  simp [outputMsgs, List.filterMap_map, Function.comp_def]

/-- **The session's framing loses nothing.** Concatenating the payloads of the frames
`outputMsgs` produces gives back exactly the ordinary output bytes it was handed.
Replay has its own incremental cursor with the same exact concatenation promise. -/
theorem outputMsgs_faithful (id : Nat) (bs : List UInt8) :
    ((outputMsgs id bs).filterMap
          (fun e =>
            match e with
            | .send _ (.output c) => some c
            | _ => none)).flatten =
      bs := by
  rw [outputMsgs_payloads id bs]
  exact chunksOf_flatten outputChunk bs

/-- **…and no frame exceeds the cap**, which is what makes every `output` message the
daemon sends well-formed by `Msg.WF`'s payload bound. -/
theorem outputMsgs_bounded (id : Nat) (bs : List UInt8) :
    ∀
      c ∈
        (outputMsgs id bs).filterMap
          (fun e =>
            match e with
            | .send _ (.output c) => some c
            | _ => none),
      c.length ≤ outputChunk := by
  rw [outputMsgs_payloads id bs]
  exact chunksOf_le outputChunk (by decide) bs

/-- **Output reaches the terminal and every attached client, exactly**: a chunk of program output
feeds the session's terminal exactly that chunk, writes the program the replies its queries ask,
then sends every client attached to the session, writable or read-only, in roster order, the same
frames, whose payloads are, in order, exactly the bytes the mediator releases, each nonempty and
at most `outputChunk` bytes, 64 KiB, and asks for nothing else. -/
theorem step_ptyOut_delivered (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.terminal = s.terminal.feed chunk ∧
      ∃ answers frames : List (List UInt8),
        (step s (.ptyOut chunk)).2 =
            answers.map Effect.writePty ++
              (s.roster.filter (·.attached)).flatMap
                (fun c => frames.map fun frame => Effect.send c.id (.output frame)) ∧
          answers.flatten = (Mediation.feed s.terminal s.scanner chunk).replies ∧
          frames.flatten = (Mediation.feed s.terminal s.scanner chunk).visible ∧
          ∀ frame ∈ frames, frame ≠ [] ∧ frame.length ≤ 65536 := by
  refine ⟨step_ptyOut_vt s chunk, ?_⟩
  rw [step_ptyOut_effects]
  simp only [State.terminal, State.scanner, State.roster]
  generalize Mediation.feed s.vt s.scan chunk = r
  refine
    ⟨if r.replies.isEmpty then [] else [r.replies],
      if r.visible.isEmpty then [] else chunksOf outputChunk r.visible, ?_, ?_, ?_, ?_⟩
  · unfold broadcast outputMsgs
    cases hr : r.replies.isEmpty <;> cases hv : r.visible.isEmpty <;> simp
  · cases hr : r.replies.isEmpty
    · simp
    · simp [List.isEmpty_iff.mp hr]
  · cases hv : r.visible.isEmpty
    · simpa using chunksOf_flatten outputChunk r.visible
    · simp [List.isEmpty_iff.mp hv]
  · intro frame hframe
    cases hv : r.visible.isEmpty
    · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hframe
      have hne : r.visible ≠ [] := fun he => by simp [he] at hv
      exact
        ⟨chunksOf_ne_nil outputChunk r.visible hne frame hframe,
          chunksOf_le outputChunk (by decide) r.visible frame hframe⟩
    · simp [hv] at hframe

/-- The cap is inclusive, with exactly one completion after all info chunks. -/
theorem infoMsgs_accepted (id : Nat) (bs : List UInt8) (h : bs.length ≤ infoReplyCap) :
    infoMsgs id bs =
      (chunksOf outputChunk bs).map (fun c => .send id (.infoReply c)) ++ [.send id .done] := by
  simp only [infoMsgs, Nat.not_lt.mpr h, ite_false]

/-- Overflow is refused before any prefix or completion can escape. -/
theorem infoMsgs_refused (id : Nat) (bs : List UInt8) (h : infoReplyCap < bs.length) :
    infoMsgs id bs =
      [.send id (.err ("info reply exceeds the byte limit".toUTF8.toList.take outputChunk))] := by
  simp only [infoMsgs, h, ite_true]

theorem infoMsgs_payloads (id : Nat) (bs : List UInt8) (h : bs.length ≤ infoReplyCap) :
    (infoMsgs id bs).filterMap
        (fun e =>
          match e with
          | .send _ (.infoReply c) => some c
          | _ => none) =
      chunksOf outputChunk bs := by
  rw [infoMsgs_accepted id bs h]
  simp [List.filterMap_map, Function.comp_def]

/-- Concatenation preserves every encoded byte, including records spanning frames. -/
theorem infoMsgs_faithful (id : Nat) (bs : List UInt8) (h : bs.length ≤ infoReplyCap) :
    ((infoMsgs id bs).filterMap
          (fun e =>
            match e with
            | .send _ (.infoReply c) => some c
            | _ => none)).flatten =
      bs := by
  rw [infoMsgs_payloads id bs h]
  exact chunksOf_flatten outputChunk bs

/-- Every emitted frame, including an error, fits both the chunk and wire bounds. -/
theorem infoMsgs_bounded (id : Nat) (bs : List UInt8) (dest : Nat) (m : Msg)
    (h : Effect.send dest m ∈ infoMsgs id bs) :
    dest = id ∧ m.payload.length ≤ outputChunk ∧ m.WF := by
  have hcap : outputChunk ≤ Wire.maxPayload := by decide
  unfold infoMsgs at h
  split at h
  · simp only [List.mem_singleton, Effect.send.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc := List.length_take_le outputChunk "info reply exceeds the byte limit".toUTF8.toList
    exact ⟨rfl, hc, Nat.le_trans hc hcap, trivial⟩
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨chunk, hc, he⟩ := List.mem_map.mp h
      simp only [Effect.send.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hc := chunksOf_le outputChunk (by decide) bs chunk hc
      exact ⟨rfl, hc, Nat.le_trans hc hcap, trivial⟩
    · simp only [List.mem_singleton, Effect.send.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Nat.zero_le _, Nat.zero_le _, trivial⟩

/-- Carry the bounds through the actual info arm that the daemon executes. -/
theorem onMsg_info_bounded (s : State) (c : Client) (dest : Nat) (m : Msg) (ha : c.answered = false)
    (h : Effect.send dest m ∈ (onMsg s c .info).2) :
    dest = c.id ∧ m.payload.length ≤ outputChunk ∧ m.WF := by
  rw [onMsg_info s c ha] at h
  exact infoMsgs_bounded c.id (infoText s) dest m h

/-- An accepted info request delivers the complete serialized fields and labels. -/
theorem onMsg_info_faithful (s : State) (c : Client) (ha : c.answered = false)
    (h : (infoText s).length ≤ infoReplyCap) :
    (((onMsg s c .info).2).filterMap
          (fun e =>
            match e with
            | .send _ (.infoReply chunk) => some chunk
            | _ => none)).flatten =
      infoText s := by
  rw [onMsg_info s c ha]
  exact infoMsgs_faithful c.id (infoText s) h

/-! ## What a session shows

The observations the headline theorems read, pinned for `Challenge.lean`: what a daemon boots
with, how `run` composes single events and finds a client, and what connecting, closing and pty
output do to them. -/

/-- A daemon boots with the terminal its checkpoint restored, or a fresh 80×24 one, no clients,
the first `maxFields` of its restored fields that are the record's own, and an idle scanner. -/
theorem boot_observed (vt : Vt.Vt) (fields metaKv : List (String × String)) :
    bootVt none = Vt.Vt.init 80 24 ∧
      bootVt (some vt) = vt ∧
      (State.boot vt fields metaKv).terminal = vt ∧
      (State.boot vt fields metaKv).roster = [] ∧
      (State.boot vt fields metaKv).fieldList = (fields.filter (recordField ·.1)).take maxFields ∧
      (State.boot vt fields metaKv).scanner = .ground := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `run` handles a trace one event at a time, and a client's record is the first in the
roster with its identifier. -/
theorem run_observed (s : State) (ev : Event) (evs : List Event) (id : Nat) :
    run s [] = (s, []) ∧
      run s (ev :: evs) =
        ((run (run s [ev]).1 evs).1, (run s [ev]).2 ++ (run (run s [ev]).1 evs).2) ∧
      s.client? id = s.roster.find? (·.id == id) := by
  refine ⟨rfl, ?_, rfl⟩
  simp [run]

/-- Tracing events through `step` is `run`: the headline theorems' fold over the transition
the driver calls is the one the session theorems are stated over. -/
theorem trace_step (s : State) (evs : List Event) : trace step s evs = run s evs := by
  induction evs generalizing s with
  | nil => rfl
  | cons ev evs ih => simp only [trace, run, ih]

/-- A connection joins a booted session's roster as a fresh record, and a booted session holds
no record: the witness that input isolation rejects a session that forgets its clients. -/
theorem connected_client_witness :
    (trace step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1.client? 1 = some { id := 1 } ∧
      (State.boot (Vt.Vt.init 1 1) [] []).client? 1 = none := ⟨rfl, rfl⟩

/-- Closing a connection removes every record with its identifier. -/
theorem closeClient_clients (s : State) (id : Nat) :
    (closeClient s id).1.clients = s.clients.filter (·.id != id) := by
  unfold closeClient; dsimp only; split <;> rfl

/-- After a close, no record has the closed identifier. -/
theorem closeClient_client? (s : State) (id : Nat) : (closeClient s id).1.client? id = none := by
  simp only [State.client?, closeClient_clients, List.find?_eq_none, List.mem_filter]
  intro c hc
  simpa using hc.2

/-- A connection the session has room for joins the end of the roster as a fresh record, and
one past `maxClients` is closed without joining; a closed connection leaves no record; pty output
reaches the terminal byte for byte; and a lone ESC from the child puts an idle scanner inside an
escape sequence. -/
theorem events_observed (s : State) (id : Nat) (chunk : List UInt8) :
    (s.roster.length < maxClients → (run s [.connected id]).1.roster = s.roster ++ [{ id }]) ∧
      (maxClients ≤ s.roster.length →
        (run s [.connected id]).1.roster = s.roster ∧ Effect.close id ∈ (run s [.connected id]).2) ∧
      (run s [.closed id]).1.client? id = none ∧
      (run s [.ptyOut chunk]).1.terminal = s.terminal.feed chunk ∧
      (s.scanner = .ground → (run s [.ptyOut [0x1B]]).1.scanner = .esc) := by
  refine ⟨fun h => ?_, fun h => ?_, ?_, ?_, fun h => ?_⟩
  · simp [run, State.roster, step_connected_admitted s id h]
  · simp [run, State.roster, step_connected_refused s id h]
  · simpa [run, step] using closeClient_client? s id
  · simp [run, State.terminal, step_ptyOut_vt]
  · simp only [State.scanner] at h
    simp [run, State.scanner, step_ptyOut_scan, Mediation.feed, h, Mediation.Scan.step]

/-! ## Read-only clients

A client that attached read-only is a watcher, whatever its terminal's size. Whatever bytes it
sends, however chunked, leave the terminal and the labels alone, and every effect they cause is a
message to it, its own disconnection or a checkpoint: it can look and leave, and nothing else.
Its records stay watchers' across the trace: no message detaches it or makes it writable, and a
decoder error removes every record with its identifier. -/

/-- An effect a watcher's bytes may cause: a message to it, its own disconnection, or a
checkpoint. -/
def watcherEffect (id : Nat) : Effect Plan → Bool
  | .send to _ | .close to => to == id
  | .checkpoint => true
  | _ => false

/-- Every record the identifier finds is attached read-only. -/
def Watches (s : State) (id : Nat) : Prop :=
  ∀ c, s.client? id = some c → c.attached = true ∧ c.mode = .readOnly

/-- The record an identifier finds decides `Watches` for it. -/
theorem watches_of_client? {s : State} {c : Client} (hc : s.client? c.id = some c)
    (ha : c.attached = true) (hs : c.mode = .readOnly) : Watches s c.id := by
  intro c' h
  rw [hc] at h
  cases h
  exact ⟨ha, hs⟩

/-- Rewriting a found record with a watcher's makes the identifier a watcher's. -/
theorem watches_setClient {s : State} {c c0 : Client} {id : Nat} (hid : c.id = id)
    (hc : s.client? id = some c0) (ha : c.attached = true) (hs : c.mode = .readOnly) :
    Watches (s.setClient c) id := by
  subst hid
  exact watches_of_client? (client?_setClient hc) ha hs

/-- A message from an attached sender keeps its record attached and its mode as it was. -/
theorem onMsg_watcher_record (s : State) (c : Client) (m : Msg) (hc : s.client? c.id = some c)
    (ha : c.attached = true) :
    ∃ c', (onMsg s c m).1.client? c.id = some c' ∧ c'.attached = c.attached ∧ c'.mode = c.mode := by
  cases m with
  | attach mode cols rows =>
    exact
      ⟨c, by
        rw [onMsg_attach_already s c mode cols rows ha]; exact hc, rfl, rfl⟩
  | resize cols rows =>
    unfold onMsg
    dsimp only
    let c1 : Client :=
      { c with
        cols, rows }
    have h1 : (s.setClient c1).client? c.id = some c1 := client?_setClient (c := c1) hc
    split
    · refine ⟨c1, ?_, rfl, rfl⟩
      unfold resizeOwned
      split
      · simp only [State.client?, resize_clients]; exact h1
      · exact h1
    · rename_i hna
      exact absurd ha hna
  | info
  | history
  | screen =>
    have h1 := client?_setClient (c := { c with answered := true }) hc
    unfold onMsg
    dsimp only
    split
    · exact ⟨c, hc, rfl, rfl⟩
    · refine ⟨{ c with answered := true }, ?_, rfl, rfl⟩
      simp only [State.client?] at h1 ⊢
      exact h1
  | wait =>
    unfold onMsg
    dsimp only
    split
    · exact ⟨c, hc, rfl, rfl⟩
    · exact
        ⟨{ c with waiting := true }, client?_setClient (c := { c with waiting := true }) hc, rfl,
          rfl⟩
  | _ =>
    refine ⟨c, ?_, rfl, rfl⟩
    unfold onMsg
    dsimp only
    repeat' split
    all_goals exact hc

/-- Every effect of a watcher's message is a message to it. -/
theorem onMsg_watcher_own (s : State) (c : Client) (m : Msg) (ha : c.attached = true)
    (hs : c.mode = .readOnly) : (onMsg s c m).2.all (watcherEffect c.id) = true := by
  cases m
  all_goals
    unfold onMsg resizeOwned resize controlResize infoMsgs
    dsimp only
    repeat' split
  all_goals simp_all [watcherEffect, outputMsgs, Client.sizes]

/-- A message from a watcher leaves the terminal alone. -/
theorem onMsg_watcher_vt (s : State) (c : Client) (m : Msg) (ha : c.attached = true)
    (hs : c.mode = .readOnly) : (onMsg s c m).1.vt = s.vt := by
  cases m
  all_goals
    unfold onMsg resizeOwned resize
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient, Client.sizes]

/-- A message from a watcher leaves the labels alone. -/
theorem onMsg_watcher_labels (s : State) (c : Client) (m : Msg) (ha : c.attached = true)
    (hs : c.mode = .readOnly) : (onMsg s c m).1.fields = s.fields := by
  cases m
  all_goals
    unfold onMsg resizeOwned resize
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient, Client.sizes]

/-- A message batch from a watcher keeps its records watchers', leaves the terminal and the
labels alone, and adds only effects a watcher may cause. -/
theorem feedMsgs_watcher (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (hw : Watches acc.1 id) (hq : acc.2.all (watcherEffect id) = true) :
    Watches (feedMsgs id msgs acc).1 id ∧
      (feedMsgs id msgs acc).1.vt = acc.1.vt ∧
      (feedMsgs id msgs acc).1.fields = acc.1.fields ∧
      (feedMsgs id msgs acc).2.all (watcherEffect id) = true := by
  apply
    feedMsgs_induct id msgs acc (P := fun r =>
      Watches r.1 id ∧
        r.1.vt = acc.1.vt ∧ r.1.fields = acc.1.fields ∧ r.2.all (watcherEffect id) = true)
      ?_ ⟨hw, rfl, rfl, hq⟩
  intro r c m _ _ _ hc ⟨hw', hvt, hlb, hq'⟩
  have hid : c.id = id := client?_id hc
  subst hid
  obtain ⟨ha, hs⟩ := hw' c hc
  obtain ⟨c', hc', ha', hs'⟩ := onMsg_watcher_record r.1 c m hc ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c'' h''
    rw [hc'] at h''
    cases h''
    exact ⟨ha'.trans ha, hs'.trans hs⟩
  · rw [onMsg_watcher_vt r.1 c m ha hs, hvt]
  · rw [onMsg_watcher_labels r.1 c m ha hs, hlb]
  · simp [List.all_append, hq', onMsg_watcher_own r.1 c m ha hs]

/-- One read from a watcher keeps its records watchers', leaves the terminal and the labels
alone, and adds only effects a watcher may cause. -/
theorem step_bytes_watcher (s : State) (id : Nat) (chunk : List UInt8) (hw : Watches s id) :
    Watches (step s (.bytes id chunk)).1 id ∧
      (step s (.bytes id chunk)).1.vt = s.vt ∧
      (step s (.bytes id chunk)).1.fields = s.fields ∧
      (step s (.bytes id chunk)).2.all (watcherEffect id) = true := by
  unfold step
  dsimp only
  split
  · exact ⟨hw, rfl, rfl, rfl⟩
  · rename_i c hc
    obtain ⟨ha, hs⟩ := hw c hc
    have hid : c.id = id := client?_id hc
    split
    · refine ⟨fun c' h' => ?_, closeClient_vt s id, closeClient_labels s id, ?_⟩
      · rw [closeClient_client?] at h'
        cases h'
      · have hcl := closeClient_watcher s id hc hs
        have hq : (closeClient s id).2.all (watcherEffect id) = true := by
          rw [List.all_eq_true]
          intro e he
          rw [hcl e he]
          rfl
        simp [List.all_cons, hq, watcherEffect]
    · have hw0 :=
        watches_setClient (c :=
          { c with
            decoder := (c.decoder.feed chunk).1, answered := false })
          hid hc ha hs
      exact
        feedMsgs_watcher id (c.decoder.feed chunk).2
          (s.setClient
              { c with
                decoder := (c.decoder.feed chunk).1, answered := false },
            [])
          hw0 rfl

/-- Bytes from a watcher, however chunked, leave the terminal and the labels alone and add only
effects a watcher may cause. -/
theorem run_bytes_watcher (s : State) (id : Nat) (chunks : List (List UInt8)) (hw : Watches s id) :
    (run s (chunks.map (Event.bytes id))).1.vt = s.vt ∧
      (run s (chunks.map (Event.bytes id))).1.fields = s.fields ∧
      (run s (chunks.map (Event.bytes id))).2.all (watcherEffect id) = true := by
  induction chunks generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons chunk rest
    ih =>
    obtain ⟨hw', hvt, hlb, hq⟩ := step_bytes_watcher s id chunk hw
    obtain ⟨hvt', hlb', hq'⟩ := ih (step s (.bytes id chunk)).1 hw'
    simp only [List.map_cons, run]
    exact ⟨hvt'.trans hvt, hlb'.trans hlb, by simp [List.all_append, hq, hq']⟩

/-- **A watcher can look and leave, and nothing else**: whatever bytes it sends, however
chunked, and whatever its terminal's size, leave the terminal and the labels unchanged, and every
effect they cause is a message to the watcher, its own disconnection or a checkpoint. -/
theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.mode = .readOnly) :
    (run s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (run s (chunks.map (Event.bytes id))).1.fieldList = s.fieldList ∧
      ∀ eff ∈ (run s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  have hw : Watches s id := by
    intro c' h
    rw [hc] at h
    cases h
    exact ⟨attached, watcher⟩
  obtain ⟨hvt, hlb, hq⟩ := run_bytes_watcher s id chunks hw
  refine ⟨hvt, hlb, fun eff he => ?_⟩
  have own := List.all_eq_true.mp hq eff he
  cases eff with
  | send to m => exact .inl ⟨m, by simp_all [watcherEffect]⟩
  | close to => exact .inr (.inl (by simp_all [watcherEffect]))
  | checkpoint => exact .inr (.inr rfl)
  | _ => simp [watcherEffect] at own

/-! ## One read and one close, as the headlines state them

The headline theorems name `step`, not the handlers it calls. A read that completes exactly one
message is that message's answer (`step_bytes_single`), so the focus reports, the refusal of an
unknown request and the one reply per read restate as `step` events. -/

/-- A read that completes exactly one message, with a healthy decoder, is that message's answer
from the sender's record with its decoder advanced and its read not yet answered. -/
theorem step_bytes_single {s : State} {id : Nat} {chunk : List UInt8} {c : Client}
    {dec : Wire.Decoder} {m : Msg} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [m])) (healthy : dec.errored = false) :
    step s (.bytes id chunk) =
      onMsg
        (s.setClient
          { c with
            decoder := dec, answered := false })
        { c with
          decoder := dec, answered := false }
        m := by
  have he :
    ({ c with
            decoder := dec, answered := false } :
          Client).id =
      id :=
    (client?_id hc : c.id = id)
  have h1 :
    (s.setClient
            { c with
              decoder := dec, answered := false }).client?
        id =
      some
        { c with
          decoder := dec, answered := false } := by
    rw [← he]; exact client?_setClient (he ▸ hc)
  simp only [step, hc, read, healthy, Bool.false_eq_true, ↓reduceIte, feedMsgs, List.foldl_cons,
    List.foldl_nil, List.contains_nil, Bool.or_self, h1, List.nil_append]

/-- A resize by the size owner asks the runtime for nothing but a pty resize. -/
theorem resizeOwned_effects (s : State) (c : Client) :
    ∀ e ∈ (resizeOwned s c).2, e.resizes = true := by
  unfold resizeOwned resize
  repeat' split
  all_goals simp [Effect.resizes]

/-- Recording a connection that is not attached leaves someone able to type exactly when someone
under another identifier could. -/
theorem focused_setClient_unattached (s : State) (c : Client) (ha : c.attached = false) :
    (s.setClient c).focused =
      s.clients.any (fun x => x.id != c.id && (x.attached && x.mode == .writable)) := by
  unfold State.focused State.setClient
  dsimp only
  generalize s.clients = l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    by_cases hx : x.id = c.id
    · simp [hx, ha]
    · have hne : (x.id != c.id) = true := bne_iff_ne.mpr hx
      have hbeq : (x.id == c.id) = false := by simpa using hx
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hne, Bool.true_and]

/-- An attach writes to the program only the focus report it owes. -/
theorem onMsg_attach_writePty (t : State) (c : Client) (mode : Mode) (cols rows : UInt32)
    (bytes : List UInt8) :
    Effect.writePty bytes ∈ (onMsg t c (.attach mode cols rows)).2 ↔
      c.attached = false ∧
        Effect.writePty bytes ∈
          focusEffects (mode == .writable) t.focused
            (resizeOwned
                {
                  t.setClient
                    { c with
                      attached := true, mode, seq := t.attachSeq, cols, rows } with
                  attachSeq := t.attachSeq + 1, lookSeq := t.outSeq, asking := false,
                  notice := none, finished := none }
                { c with
                  attached := true, mode, seq := t.attachSeq, cols, rows }).1 := by
  let c' : Client :=
    { c with
      attached := true, mode, seq := t.attachSeq, cols, rows }
  let t1 : State :=
    { t.setClient c' with
      attachSeq := t.attachSeq + 1, lookSeq := t.outSeq, asking := false, notice := none,
      finished := none }
  have hro := resizeOwned_effects t1 c'
  unfold onMsg
  dsimp only
  cases ha : c.attached
  · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    show
      Effect.writePty bytes ∈
          (resizeOwned t1 c').2 ++
            focusEffects (mode == .writable) t.focused (resizeOwned t1 c').1 ++
            _ ++
            _ ↔
        _
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
    constructor
    · rintro ((hm | hm) | hm)
      · exact absurd (hro _ hm) (by simp [Effect.resizes])
      · exact hm
      · split at hm <;> simp at hm
    · intro hm
      exact Or.inl (Or.inr hm)
  · simp

/-- **Focus follows typing, on attach**: a read that completes exactly one attach writes to the
program only `CSI I`, and exactly when the program enabled focus reporting, the attach comes from
a connection not yet attached and asks to be writable, whatever its terminal's size, and nobody
else could type. -/
theorem step_attach_focus (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.attach mode cols rows])) (healthy : dec.errored = false)
    (bytes : List UInt8) :
    Effect.writePty bytes ∈ (step s (.bytes id chunk)).2 ↔
      bytes = [0x1B, 0x5B, 0x49] ∧
        s.terminal.getModes.focusEvents = true ∧
        c.attached = false ∧
        mode = .writable ∧
        ∀ other ∈ s.roster,
          other.id ≠ id → (other.attached && other.mode == .writable) = false := by
  have hid : c.id = id := client?_id hc
  have hc' : s.client? c.id = some c := by
    rw [hid]; exact hc
  rw [step_bytes_single hc read healthy, onMsg_attach_writePty]
  let c1 : Client :=
    { c with
      decoder := dec, answered := false }
  let t := s.setClient c1
  let c' : Client :=
    { c1 with
      attached := true, mode, seq := t.attachSeq, cols, rows }
  let t1 : State :=
    { t.setClient c' with
      attachSeq := t.attachSeq + 1, lookSeq := t.outSeq, asking := false, notice := none,
      finished := none }
  show
    (c1.attached = false ∧
        Effect.writePty bytes ∈ focusEffects (mode == .writable) t.focused (resizeOwned t1 c').1) ↔
      _
  have h1 : t.client? c'.id = some c1 := client?_setClient (c := c1) hc'
  have hmodes : (resizeOwned t1 c').1.vt.getModes = s.vt.getModes := (resizeOwned_frame t1 c').2
  have hafter (hs : mode = .writable) : (resizeOwned t1 c').1.focused = true := by
    have hf : (t.setClient c').focused = true := focused_setClient (c := c') h1 rfl hs
    simp only [State.focused, (resizeOwned_frame t1 c').1]
    exact hf
  cases ha : c.attached
  · have hbefore :
      t.focused = s.clients.any (fun x => x.id != id && (x.attached && x.mode == .writable)) := by
      rw [focused_setClient_unattached s c1 ha]
      simp only [c1, hid]
    unfold focusEffects
    rw [hbefore]
    rcases (by cases mode <;> simp : mode = .readOnly ∨ mode = .writable) with hm | hm
    · simp only [hm, mode_beq, reduceCtorEq, decide_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, List.not_mem_nil, and_false, false_and]
    · rw [hafter hm, hmodes, hm]
      have key :
        s.clients.any (fun x => x.id != id && (x.attached && x.mode == .writable)) = false ↔
          ∀ other ∈ s.clients,
            other.id ≠ id → (other.attached && other.mode == .writable) = false := by
        rw [List.any_eq_false]
        constructor
        · intro h other hother hne
          simpa [bne_iff_ne, hne] using h other hother
        · intro h other hother
          by_cases hne : other.id = id
          · simp [hne]
          · simpa [bne_iff_ne, hne] using h other hother hne
      simp only [State.terminal, State.roster]
      rw [← key]
      generalize s.clients.any (fun x => x.id != id && (x.attached && x.mode == .writable)) = A
      generalize s.vt.getModes.focusEvents = fe
      cases A <;> cases fe <;> simp [focusReport]
  · simp

/-- **…and on close**: closing a connection writes to the program only `CSI O`, and exactly when
the program enabled focus reporting and the connection, which was writable, was the last
through which someone could type. -/
theorem step_closed_focus (s : State) (id : Nat) (bytes : List UInt8) :
    Effect.writePty bytes ∈ (step s (.closed id)).2 ↔
      bytes = [0x1B, 0x5B, 0x4F] ∧
        s.terminal.getModes.focusEvents = true ∧
        (s.client? id).any (·.mode == .writable) = true ∧
        s.roster.any (fun c => c.attached && c.mode == .writable) = true ∧
        (step s (.closed id)).1.roster.any (fun c => c.attached && c.mode == .writable) =
          false := by
  have hroster : (step s (.closed id)).1.roster = s.clients.filter (·.id != id) :=
    closeClient_clients s id
  rw [hroster]
  have hsub :
    (s.clients.filter (·.id != id)).any (fun c => c.attached && c.mode == .writable) = true →
      s.clients.any (fun c => c.attached && c.mode == .writable) = true := by
    simp only [List.any_eq_true, List.mem_filter]
    rintro ⟨x, ⟨hx, -⟩, h⟩
    exact ⟨x, hx, h⟩
  have hfx :
    Effect.writePty bytes ∈ (step s (.closed id)).2 ↔
      Effect.writePty bytes ∈
        focusEffects ((s.client? id).any (·.mode == .writable)) s.focused (s.dropClient id) := by
    show Effect.writePty bytes ∈ (closeClient s id).2 ↔ _
    unfold closeClient
    dsimp only
    split <;> simp
  rw [hfx]
  have hsub' : (s.dropClient id).focused = true → s.focused = true := hsub
  unfold focusEffects
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
    obtain ⟨⟨htyp, hne⟩, hmode⟩ := hcond
    have hafter : (s.dropClient id).focused = false := by
      cases h : (s.dropClient id).focused
      · rfl
      · exact absurd (by rw [h, hsub' h]) hne
    have hbefore : s.focused = true := by
      cases h : s.focused
      · exact absurd (by rw [h, hafter]) hne
      · rfl
    rw [List.mem_singleton, Effect.writePty.injEq, hafter]
    exact ⟨fun hb => ⟨hb, hmode, htyp, hbefore, hafter⟩, fun h => h.1⟩
  · rename_i hcond
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨-, hmode, htyp, hbefore, hafter⟩
    apply hcond
    have hb : s.focused = true := hbefore
    have ha : (s.dropClient id).focused = false := hafter
    have hm : (s.dropClient id).vt.getModes.focusEvents = true := hmode
    rw [htyp, hb, ha, hm]
    rfl

/-- **An unknown request is refused**: a read that completes exactly one message this version does
not know gets the reason, and the session's terminal and labels stay as they were. -/
theorem step_unknown_refused (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {tag : UInt8} {payload : List UInt8} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.unknown tag payload])) (healthy : dec.errored = false) :
    (step s (.bytes id chunk)).2 = [.send id (.err "unknown message".toUTF8.toList)] ∧
      (step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (step s (.bytes id chunk)).1.fieldList = s.fieldList := by
  have hid : c.id = id := client?_id hc
  rw [step_bytes_single hc read healthy, onMsg_unknown]
  exact ⟨by simp [hid], rfl, rfl⟩

/-- **A kill stops the program, and nothing after it takes effect**: a read whose first message
is a kill, from a client that may send one, stops the program and closes the client's
connection, whatever the read holds after the kill, and the session's terminal and labels stay
as they were. -/
theorem step_kill_stops (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {rest : List Msg} (hc : s.client? id = some c)
    (writable : c.mode = .writable) (read : c.decoder.feed chunk = (dec, .kill :: rest))
    (healthy : dec.errored = false) :
    (step s (.bytes id chunk)).2 = [.stopProgram, .close id] ∧
      (step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (step s (.bytes id chunk)).1.fieldList = s.fieldList := by
  have he :
    ({ c with
            decoder := dec, answered := false } :
          Client).id =
      id :=
    (client?_id hc : c.id = id)
  have h1 :
    (s.setClient
            { c with
              decoder := dec, answered := false }).client?
        id =
      some
        { c with
          decoder := dec, answered := false } := by
    rw [← he]; exact client?_setClient (he ▸ hc)
  have killed :
    onMsg
        (s.setClient
          { c with
            decoder := dec, answered := false })
        { c with
          decoder := dec, answered := false }
        .kill =
      (s.setClient
          { c with
            decoder := dec, answered := false },
        [.stopProgram, .close id]) := by
    rw [onMsg_kill]
    simp [writable, ← he]
  have first :
    step s (.bytes id chunk) =
      feedMsgs id rest
        (s.setClient
            { c with
              decoder := dec, answered := false },
          [.stopProgram, .close id]) := by
    simp only [step, hc, read, healthy, Bool.false_eq_true, ↓reduceIte]
    rw [show (Msg.kill :: rest) = [.kill] ++ rest from rfl, feedMsgs_append]
    simp only [feedMsgs, List.foldl_cons, List.foldl_nil, List.contains_nil, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte, h1, killed, List.nil_append]
  rw [first, feedMsgs_after_close id rest _ (by simp)]
  exact ⟨rfl, rfl, rfl⟩

/-- No message stops the daemon: only the end of its program does. -/
theorem onMsg_no_exit (s : State) (c : Client) (m : Msg) : Effect.exit ∉ (onMsg s c m).2 := by
  cases m
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp

/-- A read never stops the daemon. -/
theorem step_bytes_no_exit (s : State) (id : Nat) (chunk : List UInt8) :
    Effect.exit ∉ (step s (.bytes id chunk)).2 := by
  simp only [step]
  split
  · simp
  · split
    · intro h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · rcases closed_effects s id _ (by simpa only [step] using h) with h | h <;> cases h
    · exact
        feedMsgs_induct _ _ _ (P := fun acc => Effect.exit ∉ acc.2)
          (fun acc c m _ _ _ _ hacc h => by
            rcases List.mem_append.mp h with h | h
            · exact hacc h
            · exact onMsg_no_exit acc.1 c m h)
          (by simp)

/-- **A session ends only through an ending**: an event stops the daemon exactly when it ends the
session (`Event.ends`): the end of the program, by itself or once the daemon stopped it, or a stop
signal to the daemon. -/
theorem step_exit_iff (s : State) (ev : Event) (seen : Bool) :
    Effect.exit ∈ (step s ev).2 ↔ (ev.ends seen).isSome := by
  constructor
  · intro h
    cases ev with
    | childExited o => rfl
    | stopped o => rfl
    | signal n => rfl
    | bytes id chunk => exact absurd h (step_bytes_no_exit s id chunk)
    | closed id => rcases closed_effects s id _ h with h | h <;> cases h
    | connected id =>
      simp only [step] at h
      split at h <;> simp at h
    | ptyOut chunk =>
      rw [step_ptyOut_effects] at h
      dsimp only at h
      rcases List.mem_append.mp h with h | h
      · split at h <;> simp at h
      · exact absurd h (broadcast_no_exit _ _)
    | tick now =>
      simp only [step] at h
      split at h <;> simp at h
    | checkpointFailed => simp [checkpointFailed_effects] at h
    | observed o => simp [step] at h
  · intro h
    cases ev with
    | childExited o => simp [step_childExited_effects, conclude_effects]
    | stopped o => simp [step_stopped_effects, conclude_effects]
    | signal n => simp [step_signal_effects, conclude_effects]
    | _ => simp [Event.ends] at h

/-- **Every ending is told, and one ending ends every session**: an event stops the daemon exactly
when it ends the session, and then its effects end with one tail, the end record saying how it
ended and then the save that keeps the session or the delete that discards it, as the ending
decides, and the exit; before the tail nothing saves or deletes the checkpoint, every client
attached or waiting hears how the session ended, and the terminal the ending saves is the one it
found. -/
theorem step_ended_reports (s : State) (ev : Event) :
    (Effect.exit ∈ (step s ev).2 ↔ (ev.ends (seenBy s.roster)).isSome) ∧
      ∀ e keep,
        ev.ends (seenBy s.roster) = some (e, keep) →
          ∃ front,
            (step s ev).2 =
                front ++
                  [.record e.record, if keep then Effect.checkpoint else Effect.dropCheckpoint,
                    .exit] ∧
              Effect.checkpoint ∉ front ∧
              Effect.dropCheckpoint ∉ front ∧
              (∀ c ∈ s.roster,
                c.attached = true ∨ c.waiting = true → e.told.map (Effect.send c.id) <:+: front) ∧
              (step s ev).1.terminal = s.terminal := by
  refine ⟨step_exit_iff s ev _, fun e keep ends => ?_⟩
  have shaped (front : List (Effect Plan))
    (only : ∀ eff ∈ front, (∃ id m, eff = .send id m) ∨ ∃ id, eff = .close id) :
    Effect.checkpoint ∉ front ∧ Effect.dropCheckpoint ∉ front :=
    ⟨(front_quiet only).1, (front_quiet only).2.1⟩
  cases ev with
  | childExited o =>
    simp only [Event.ends, Option.some.injEq, Prod.mk.injEq] at ends
    obtain ⟨rfl, rfl⟩ := ends
    obtain ⟨front, effects, only, heard⟩ := conclude_shape s (.program o) (!seenBy s.roster)
    exact ⟨front, effects, (shaped front only).1, (shaped front only).2, heard, rfl⟩
  | stopped o =>
    simp only [Event.ends, Option.some.injEq, Prod.mk.injEq] at ends
    obtain ⟨rfl, rfl⟩ := ends
    obtain ⟨front, effects, only, heard⟩ := conclude_shape s (.program o) false
    exact ⟨front, effects, (shaped front only).1, (shaped front only).2, heard, rfl⟩
  | signal n =>
    simp only [Event.ends, Option.some.injEq, Prod.mk.injEq] at ends
    obtain ⟨rfl, rfl⟩ := ends
    obtain ⟨front, effects, only, heard⟩ := conclude_shape s (.saved n) true
    refine ⟨.stopProgram :: front, ?_, ?_, ?_, fun c hc listening => ?_, rfl⟩
    · rw [step_signal_effects, effects]
      rfl
    · simpa using (shaped front only).1
    · simpa using (shaped front only).2
    · exact (heard c hc listening).trans (List.suffix_cons _ _).isInfix
  | _ => simp [Event.ends] at ends

/-- Each message's answer renders frames only as one reply: a run of frames, then `done`. -/
theorem onMsg_rendered_run (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).2.all (!·.rendered) ∨
      ∃ frames, (onMsg s c m).2 = frames ++ [.send c.id .done] ∧ frames.all (·.rendered) := by
  cases m
  case info =>
    unfold onMsg infoMsgs
    dsimp only
    split
    · exact Or.inl (by simp [Effect.rendered])
    · split
      · exact Or.inl (by simp [Effect.rendered])
      · exact Or.inr ⟨_, rfl, by simp [Effect.rendered]⟩
  case history =>
    unfold onMsg outputMsgs
    dsimp only
    split
    · exact Or.inl (by simp [Effect.rendered])
    · exact Or.inr ⟨_, rfl, by simp [Effect.rendered]⟩
  case screen =>
    unfold onMsg outputMsgs
    dsimp only
    split
    · exact Or.inl (by simp [Effect.rendered])
    · exact Or.inr ⟨_, rfl, by simp [Effect.rendered]⟩
  all_goals
    left
    unfold onMsg controlResize resizeOwned resize focusEffects
    dsimp only
    repeat' split
  all_goals simp_all [Effect.rendered]
  all_goals
    intro m told
    rcases told_mem told with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Filtering by a test that holds nowhere keeps nothing. -/
theorem filter_false_nil {α : Type} (l : List α) : l.filter (fun _ => false) = [] :=
  List.filter_eq_nil_iff.mpr (by simp)

/-- Each message's answer resizes the pty at most once. -/
theorem onMsg_resizes_le (s : State) (c : Client) (m : Msg) :
    ((onMsg s c m).2.filter (·.resizes)).length ≤ 1 := by
  cases m
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals
    simp_all [Effect.resizes, List.filter_append, List.filter_map, Function.comp_def,
      filter_false_nil]

/-- **One reply per read, as the headline states it**: the frames one read renders are one run
closed by `done`, and while its connection stays unattached it resizes the pty at most once. -/
theorem step_bytes_one_reply_observed (s : State) (id : Nat) (chunk : List UInt8) :
    ((step s (.bytes id chunk)).2.all (!·.rendered) ∨
        ∃ pre frames post,
          (step s (.bytes id chunk)).2 = pre ++ frames ++ Effect.send id .done :: post ∧
            frames.all (·.rendered) ∧ (pre ++ post).all (!·.rendered)) ∧
      (((step s (.bytes id chunk)).1.client? id).all (!·.attached) →
        ((step s (.bytes id chunk)).2.filter (·.resizes)).length ≤ 1) := by
  obtain ⟨pre, ans, post, he, hans, hf, hr⟩ := step_bytes_one_reply s id chunk
  rw [he]
  have hnone (l : List (Effect Plan)) (h : l.all (!·.resizes) = true) :
    (l.filter (·.resizes)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro e he
    simpa using (List.all_eq_true.mp h) e he
  rcases hans with rfl | ⟨c, t, c', m, -, -, ht, rfl⟩
  · refine ⟨Or.inl (by simpa using hf), fun hu => ?_⟩
    have h0 := hnone _ (hr hu)
    simp only [List.append_nil]
    omega
  · have hid := client?_id ht
    refine ⟨?_, fun hu => ?_⟩
    · rcases onMsg_rendered_run t c' m with h | ⟨frames, hfr, hall⟩
      · left
        simp only [List.all_append, Bool.and_eq_true] at hf ⊢
        exact ⟨⟨hf.1, h⟩, hf.2⟩
      · right
        exact
          ⟨pre, frames, post, by
            rw [hfr, hid]; simp, hall, hf⟩
    · have h1 := onMsg_resizes_le t c' m
      have h2 := hr hu
      simp only [List.all_append, Bool.and_eq_true] at h2
      have hp := hnone pre h2.1
      have hq := hnone post h2.2
      simp only [List.filter_append, List.length_append]
      omega

/-- A fresh connection's decoder reads a message the encoder may send back from its bytes in one
chunk: the read the per-read headlines' kills are shown with. -/
theorem feed_encode_fresh (m : Msg) (hm : m.Fits) :
    ({ id := 1 } : Client).decoder.feed (Wire.encode m) = ({}, [m]) := by
  have := Wire.decode_encode_stream [m] (by simpa using Wire.fits_wf m hm)
  simpa [Wire.decode] using this

/-! ## One source for what a session reports

The labels change only through a label request from a client that is not a watcher, the boot
metadata never changes, and only program output feeds the terminal: every other event keeps it
or resizes it. -/

/-- A message that is no label request leaves the labels as they were. -/
theorem onMsg_labels_kept (s : State) (c : Client) (m : Msg) (h : ¬m.Describes) :
    (onMsg s c m).1.fields = s.fields := by
  cases m
  all_goals simp only [Msg.Describes, not_true_eq_false] at h
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- A batch with no label request leaves the labels as they were. -/
theorem feedMsgs_labels (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (none : ∀ m ∈ msgs, ¬m.Describes) : (feedMsgs id msgs acc).1.fields = acc.1.fields := by
  exact
    feedMsgs_induct id msgs acc (P := fun r => r.1.fields = acc.1.fields)
      (fun current c m hm _ _ _ hs => (onMsg_labels_kept current.1 c m (none m hm)).trans hs) rfl

/-- **The labels have one source**: an event that changes them is a read, from a client that is
not a watcher, that holds a label request. -/
theorem step_labels_sources (s : State) (ev : Event)
    (changed : (step s ev).1.fieldList ≠ s.fieldList) :
    ∃ id chunk c,
      ev = .bytes id chunk ∧
        s.client? id = some c ∧
        (c.attached = false ∨ c.mode = .writable) ∧
        ∃ m ∈ (c.decoder.feed chunk).2, m.Describes := by
  cases ev with
  | bytes id chunk =>
    cases hc : s.client? id with
    | none => exact absurd (by simp [step, hc, State.fieldList]) changed
    | some c =>
      refine ⟨id, chunk, c, rfl, hc, ?_, ?_⟩
      · by_cases hw : c.attached = true ∧ c.mode = .readOnly
        · have hwatch : Watches s id := by
            intro c' h'
            rw [hc] at h'
            cases h'
            exact hw
          exact absurd (step_bytes_watcher s id chunk hwatch).2.2.1 changed
        · cases ha : c.attached <;> cases hs : c.mode <;> simp_all
      · apply Classical.byContradiction
        intro hnone
        apply changed
        simp only [not_exists, not_and] at hnone
        simp only [step, hc, State.fieldList]
        split
        · simp
        · rw [feedMsgs_labels]
          · simp [State.setClient]
          · exact fun m hm => hnone m hm
  | connected id =>
    refine absurd ?_ changed
    dsimp only [step]
    split <;> rfl
  | closed id => exact absurd (by simp [step, State.fieldList]) changed
  | ptyOut chunk => exact absurd rfl changed
  | childExited o => exact absurd rfl changed
  | stopped o => exact absurd rfl changed
  | signal n => exact absurd rfl changed
  | tick now =>
    refine absurd ?_ changed
    dsimp only [step]
    split <;> rfl
  | checkpointFailed => exact absurd rfl changed
  | observed o => exact absurd rfl changed

/-- Closing a connection keeps the boot metadata. -/
theorem closeClient_metaKv (s : State) (id : Nat) : (closeClient s id).1.metaKv = s.metaKv := by
  unfold closeClient; dsimp only; split <;> rfl

/-- No message changes the boot metadata. -/
theorem onMsg_metaKv (s : State) (c : Client) (m : Msg) : (onMsg s c m).1.metaKv = s.metaKv := by
  cases m
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- No event changes the boot metadata. -/
theorem step_metaKv (s : State) (ev : Event) : (step s ev).1.metaKv = s.metaKv := by
  cases ev with
  | bytes id chunk =>
    dsimp only [step]
    split
    · rfl
    · split
      · simp [closeClient_metaKv]
      · exact
          feedMsgs_preserves _ _ _ (P := fun t => t.metaKv = s.metaKv)
            (fun t _ m _ ht => (onMsg_metaKv t _ m).trans ht) rfl
  | connected id =>
    dsimp only [step]
    split <;> rfl
  | closed id => simp [step, closeClient_metaKv]
  | tick now =>
    dsimp only [step]
    split <;> rfl
  | _ => rfl

/-- **The boot metadata has one source, the daemon that booted the session**: whatever events
follow, `info` starts with the metadata the daemon booted with. -/
theorem run_boot_infoFields (vt : Vt.Vt) (labels metaKv : List (String × String))
    (evs : List Event) :
    ∃ rest, infoFields (run (State.boot vt labels metaKv) evs).1 = metaKv ++ rest := by
  have kept : ∀ (s : State) (evs : List Event), (run s evs).1.metaKv = s.metaKv := by
    intro s evs
    induction evs generalizing s with
    | nil => rfl
    | cons ev evs ih =>
      simp only [run]
      rw [ih, step_metaKv]
  refine ⟨?rest, ?eq⟩
  case eq =>
    simp only [infoFields, kept, List.append_assoc]
    rfl

/-- A daemon boots with the metadata it is given. -/
theorem boot_metaKv (vt : Vt.Vt) (labels metaKv : List (String × String)) :
    (State.boot vt labels metaKv).metaKv = metaKv := rfl

/-- `info` starts with the boot metadata, then the number of attached clients. -/
theorem infoFields_metaKv (s : State) :
    ∃ rest,
      infoFields s =
        s.metaKv ++ ("clients", toString (s.roster.filter (·.attached)).length) :: rest := by
  refine ⟨?rest, ?eq⟩
  case eq =>
    simp only [infoFields, List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- **The terminal has one source, the program**: only program output feeds it, and every other
event keeps it or resizes it. -/
theorem step_vt_sources (s : State) (ev : Event) :
    (∃ chunk, ev = .ptyOut chunk ∧ (step s ev).1.vt = s.vt.feed chunk) ∨
      ∃ sizes : List (Nat × Nat),
        (step s ev).1.vt =
          sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.vt := by
  let Sized : Vt.Vt → Prop := fun vt =>
    ∃ sizes : List (Nat × Nat),
      vt = sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.vt
  have hresize : ∀ vt cols rows, Sized vt → Sized (vt.resize cols rows) := by
    rintro vt cols rows ⟨sizes, rfl⟩
    exact ⟨sizes ++ [(cols, rows)], by simp⟩
  have kept : Sized s.vt := ⟨[], rfl⟩
  cases ev with
  | ptyOut chunk => exact .inl ⟨chunk, rfl, step_ptyOut_vt s chunk⟩
  | bytes id chunk =>
    right
    show Sized (step s (.bytes id chunk)).1.vt
    dsimp only [step]
    split
    · exact kept
    · split
      · simpa only [closeClient_vt] using kept
      · exact
          feedMsgs_preserves _ _ _ (P := fun t => Sized t.vt)
            (fun _ _ m _ hs => onMsg_vt_preserves hresize m hs) kept
  | connected id =>
    right
    show Sized (step s (.connected id)).1.vt
    dsimp only [step]
    split <;> exact kept
  | closed id =>
    right
    show Sized (step s (.closed id)).1.vt
    simpa only [step, closeClient_vt] using kept
  | childExited o => exact .inr kept
  | stopped o => exact .inr kept
  | signal n => exact .inr kept
  | tick now =>
    right
    show Sized (step s (.tick now)).1.vt
    dsimp only [step]
    split <;> exact kept
  | checkpointFailed => exact .inr kept
  | observed o => exact .inr kept

/-- Resizes keep a cursor at the origin there: the witness that the terminal's one source
rejects a session that prints on its own. -/
theorem foldl_resize_origin (v : Vt.Vt) (h : v.cursorPos = (0, 0)) (sizes : List (Nat × Nat)) :
    (sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) v).cursorPos = (0, 0) := by
  induction sizes generalizing v with
  | nil => exact h
  | cons size sizes ih =>
    apply ih
    simp only [Vt.Vt.cursorPos, Prod.mk.injEq] at h ⊢
    simp [Vt.Vt.resize, h.1, h.2]

/-! ## A typist's input is written exactly -/

/-- Input messages from a client that may type become one write each, in order. -/
theorem feedMsgs_inputs (id : Nat) (inputs : List (List UInt8)) (t : State) (c : Client)
    (hc : t.client? id = some c) (typist : c.mode = .writable) (effs : List (Effect Plan))
    (clean : Effect.close id ∉ effs ∧ Effect.exit ∉ effs) :
    feedMsgs id (inputs.map Msg.input) (t, effs) = (t, effs ++ inputs.map Effect.writePty) := by
  induction inputs generalizing effs with
  | nil => simp [feedMsgs]
  | cons bytes inputs
    ih =>
    have stays : onMsg t c (.input bytes) = (t, [.writePty bytes]) := onMsg_input t c bytes typist
    have next := ih (effs ++ [.writePty bytes]) (by simpa using clean)
    simp only [feedMsgs, List.map_cons, List.foldl_cons] at next ⊢
    simp only [List.contains_eq_mem, decide_eq_true_eq, clean.1, clean.2, Bool.or_self, ↓reduceIte,
      hc, stays] at ⊢
    simpa using next

/-- **A typist's input is written exactly**: a read of input messages from a client that may
type is one write per message, its bytes, in order, and nothing else. -/
theorem step_input_exact (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {inputs : List (List UInt8)} (hc : s.client? id = some c)
    (typist : c.mode = .writable) (read : c.decoder.feed chunk = (dec, inputs.map Msg.input))
    (healthy : dec.errored = false) :
    (step s (.bytes id chunk)).2 = inputs.map Effect.writePty := by
  have he :
    ({ c with
            decoder := dec, answered := false } :
          Client).id =
      id :=
    (client?_id hc : c.id = id)
  have h1 :
    (s.setClient
            { c with
              decoder := dec, answered := false }).client?
        id =
      some
        { c with
          decoder := dec, answered := false } := by
    rw [← he]; exact client?_setClient (he ▸ hc)
  have :=
    feedMsgs_inputs id inputs
      (s.setClient
        { c with
          decoder := dec, answered := false })
      { c with
        decoder := dec, answered := false }
      h1 typist [] (by simp)
  simp only [step, hc, read, healthy, Bool.false_eq_true, ↓reduceIte, this, List.nil_append]

/-! ## Rights follow the mode, and only a real size reaches the pty

A connection's rights are the mode it attached with: an attach records the mode it asks for,
whatever size it gives, and a resize records its size and leaves the mode alone. A client sizes
the session only while its terminal has a size, so every pty resize has positive dimensions. -/

/-- An attach from a connection not yet attached records the mode, size and attach order it
gives, whatever that size. -/
theorem onMsg_attach_record (s : State) (c : Client) (mode : Mode) (cols rows : UInt32)
    (hc : s.client? c.id = some c) (fresh : c.attached = false) :
    (onMsg s c (.attach mode cols rows)).1.client? c.id =
      some
        { c with
          attached := true, mode, seq := s.attachSeq, cols, rows } := by
  let c' : Client :=
    { c with
      attached := true, mode, seq := s.attachSeq, cols, rows }
  have h1 : (s.setClient c').client? c.id = some c' := client?_setClient (c := c') hc
  unfold onMsg
  dsimp only
  simp only [fresh, Bool.false_eq_true, ↓reduceIte]
  unfold resizeOwned
  split
  · simp only [State.client?, resize_clients]; exact h1
  · exact h1

/-- **The rights after an attach are the mode asked for, whatever the size**: a read that
completes exactly one attach, from a connection not yet attached, leaves its record attached with
the mode and size the attach gives, the next attach order, its decoder advanced and its read not
yet answered. -/
theorem step_attach_record {s : State} {id : Nat} {chunk : List UInt8} {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    (step s (.bytes id chunk)).1.client? id =
      some
        { c with
          decoder := dec, answered := false, attached := true, mode, seq := s.attachSeq, cols,
          rows } := by
  have he :
    ({ c with
            decoder := dec, answered := false } :
          Client).id =
      id :=
    (client?_id hc : c.id = id)
  have h1 :
    (s.setClient
            { c with
              decoder := dec, answered := false }).client?
        ({ c with
              decoder := dec, answered := false } :
            Client).id =
      some
        { c with
          decoder := dec, answered := false } :=
    client?_setClient (he ▸ hc)
  rw [step_bytes_single hc read healthy, ← he]
  exact onMsg_attach_record _ _ mode cols rows h1 fresh

/-- The rights after an attach are exactly the mode it asks for, for every size. -/
theorem step_attach_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    ∃ c', (step s (.bytes id chunk)).1.client? id = some c' ∧ c'.attached = true ∧ c'.mode = mode :=
  ⟨_, step_attach_record hc fresh read healthy, rfl, rfl⟩

/-- An attach from a connection not yet attached streams it the repaint of the terminal the
attach leaves, after only the pty's resize and the program's focus report. -/
theorem onMsg_attach_repaint (t : State) (c : Client) (mode : Mode) (cols rows : UInt32)
    (fresh : c.attached = false) :
    ∃ pty,
      pty ++ [Effect.replay c.id (Replay.start (onMsg t c (.attach mode cols rows)).1.vt)] <+:
          (onMsg t c (.attach mode cols rows)).2 ∧
        ∀ eff ∈ pty,
          (∃ bytes, eff = .writePty bytes) ∨ ∃ cols rows, eff = .resizePty cols rows := by
  let c' : Client :=
    { c with
      attached := true, mode, seq := t.attachSeq, cols, rows }
  let t1 : State :=
    { t.setClient c' with
      attachSeq := t.attachSeq + 1, lookSeq := t.outSeq, asking := false, notice := none,
      finished := none }
  have hro := resizeOwned_effects t1 c'
  unfold onMsg
  simp only [fresh, Bool.false_eq_true, ↓reduceIte]
  refine
    ⟨(resizeOwned t1 c').2 ++ focusEffects (mode == .writable) t.focused (resizeOwned t1 c').1,
      List.prefix_append _ _, ?_⟩
  intro eff h
  rcases List.mem_append.mp h with h | h
  · right
    have := hro eff h
    cases eff <;> simp_all [Effect.resizes]
  · left
    unfold focusEffects at h
    split at h
    · exact ⟨_, List.mem_singleton.mp h⟩
    · simp at h

/-- **An attach repaints**: a read that completes exactly one attach, from a connection not yet
attached, streams it the repaint of the session's terminal as the attach leaves it, and nothing
the session sends it comes first: only the pty's resize and the program's focus report precede
the repaint. -/
theorem step_attach_repaint (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    ∃ pty after,
      (step s (.bytes id chunk)).2 =
          pty ++ Effect.replay id (Replay.start (step s (.bytes id chunk)).1.terminal) :: after ∧
        ∀ eff ∈ pty,
          (∃ bytes, eff = .writePty bytes) ∨ ∃ cols rows, eff = .resizePty cols rows := by
  have he :
    ({ c with
            decoder := dec, answered := false } :
          Client).id =
      id :=
    (client?_id hc : c.id = id)
  rw [step_bytes_single hc read healthy]
  obtain ⟨pty, ⟨after, effects⟩, front⟩ :=
    onMsg_attach_repaint
      (s.setClient
        { c with
          decoder := dec, answered := false })
      { c with
        decoder := dec, answered := false }
      mode cols rows fresh
  refine ⟨pty, after, ?_, front⟩
  rw [← effects, he, List.append_assoc, List.singleton_append]
  rfl

/-- A resize records its size, 0 included, and keeps the sender's mode, whether its connection
is attached or not. -/
theorem onMsg_resize_mode (s : State) (c : Client) (cols rows : UInt32)
    (hc : s.client? c.id = some c) :
    ∃ c', (onMsg s c (.resize cols rows)).1.client? c.id = some c' ∧ c'.mode = c.mode := by
  unfold onMsg
  dsimp only
  let c1 : Client :=
    { c with
      cols, rows }
  let c2 : Client := { c1 with answered := true }
  have h1 : (s.setClient c1).client? c.id = some c1 := client?_setClient (c := c1) hc
  have h2 : ((s.setClient c1).setClient c2).client? c.id = some c2 := client?_setClient (c := c2) h1
  split
  · refine ⟨c1, ?_, rfl⟩
    unfold resizeOwned
    split
    · simp only [State.client?, resize_clients]; exact h1
    · exact h1
  · split
    · exact ⟨c1, h1, rfl⟩
    · refine ⟨c2, ?_, rfl⟩
      unfold controlResize
      split
      · exact h2
      · split
        · exact h2
        · simp only [State.client?, resize_clients]; exact h2

/-- An attached client's resize records the size it gives, 0 included, and changes nothing else
of its record. -/
theorem onMsg_resize_record (s : State) (c : Client) (cols rows : UInt32)
    (hc : s.client? c.id = some c) (attached : c.attached = true) :
    (onMsg s c (.resize cols rows)).1.client? c.id =
      some
        { c with
          cols, rows } := by
  have h1 :
    (s.setClient
            { c with
              cols, rows }).client?
        c.id =
      some
        { c with
          cols, rows } :=
    client?_setClient hc
  unfold onMsg
  dsimp only
  split
  · unfold resizeOwned
    split
    · simp only [State.client?, resize_clients]; exact h1
    · exact h1
  · rename_i detached
    exact absurd attached detached

/-- A read that completes exactly one resize, from an attached client, records the size it gives,
0 included, and leaves the rest of the record as it was, its decoder advanced. -/
theorem step_resize_record {s : State} {id : Nat} {chunk : List UInt8} {c : Client}
    {dec : Wire.Decoder} {cols rows : UInt32} (hc : s.client? id = some c)
    (attached : c.attached = true) (read : c.decoder.feed chunk = (dec, [.resize cols rows]))
    (healthy : dec.errored = false) :
    (step s (.bytes id chunk)).1.client? id =
      some
        { c with
          decoder := dec, answered := false, cols, rows } := by
  have he :
    ({ c with
            decoder := dec, answered := false } :
          Client).id =
      id :=
    (client?_id hc : c.id = id)
  have h1 :
    (s.setClient
            { c with
              decoder := dec, answered := false }).client?
        ({ c with
              decoder := dec, answered := false } :
            Client).id =
      some
        { c with
          decoder := dec, answered := false } :=
    client?_setClient (he ▸ hc)
  rw [step_bytes_single hc read healthy, ← he]
  exact onMsg_resize_record _ _ cols rows h1 attached

/-- **A resize never changes a client's rights**: a read of resize messages, whatever sizes they
give, 0 included, leaves the sender's mode as it was. -/
theorem step_resize_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {sizes : List (UInt32 × UInt32)} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, sizes.map fun size => .resize size.1 size.2))
    (healthy : dec.errored = false) :
    ((step s (.bytes id chunk)).1.client? id).map (·.mode) = some c.mode := by
  have he :
    ({ c with
            decoder := dec, answered := false } :
          Client).id =
      id :=
    (client?_id hc : c.id = id)
  have h1 :
    (s.setClient
            { c with
              decoder := dec, answered := false }).client?
        id =
      some
        { c with
          decoder := dec, answered := false } := by
    rw [← he]; exact client?_setClient (he ▸ hc)
  have kept :
    ∃ c',
      (feedMsgs id (sizes.map fun size => .resize size.1 size.2)
                (s.setClient
                    { c with
                      decoder := dec, answered := false },
                  [])).1.client?
            id =
          some c' ∧
        c'.mode = c.mode := by
    refine
      feedMsgs_induct id _ _ (P := fun acc => ∃ c', acc.1.client? id = some c' ∧ c'.mode = c.mode)
        ?_ ⟨_, h1, rfl⟩
    intro acc c0 m hm _ _ hc0 ⟨c', hc', hmode⟩
    obtain ⟨size, -, rfl⟩ := List.mem_map.mp hm
    have same : c0 = c' := Option.some.inj (hc0.symm.trans hc')
    subst same
    have hid0 : c0.id = id := client?_id hc0
    obtain ⟨c'', h'', hmode''⟩ := onMsg_resize_mode acc.1 c0 size.1 size.2 (hid0 ▸ hc0)
    exact ⟨c'', hid0 ▸ h'', hmode''.trans hmode⟩
  obtain ⟨c', hc', hmode⟩ := kept
  have first :
    step s (.bytes id chunk) =
      feedMsgs id (sizes.map fun size => .resize size.1 size.2)
        (s.setClient
            { c with
              decoder := dec, answered := false },
          []) := by
    simp only [step, hc, read, healthy, Bool.false_eq_true, ↓reduceIte]
  rw [first, hc', Option.map_some, hmode]

/-- A resize asks the pty for the size it is given, clamped by `Vt.clampDim`. -/
theorem resize_source (s : State) (cols rows ec er : UInt32)
    (h : Effect.resizePty ec er ∈ (resize s cols rows).2) :
    ec.toNat = Vt.clampDim cols.toNat ∧ er.toNat = Vt.clampDim rows.toNat := by
  have agrees := resize_agrees s cols rows ec er h
  revert h agrees
  unfold resize
  split
  · simp
  · intro _ agrees
    exact agrees

/-- The size owner's resize is its own size, clamped, and a real one. -/
theorem resizeOwned_source (s : State) (c : Client) (ec er : UInt32)
    (h : Effect.resizePty ec er ∈ (resizeOwned s c).2) :
    c.cols ≠ 0 ∧
      c.rows ≠ 0 ∧ ec.toNat = Vt.clampDim c.cols.toNat ∧ er.toNat = Vt.clampDim c.rows.toNat := by
  unfold resizeOwned at h
  split at h
  · rename_i owner
    obtain ⟨hc, hr⟩ := resize_source s c.cols c.rows ec er h
    refine ⟨fun zero => ?_, fun zero => ?_, hc, hr⟩ <;> simp [Client.sizes, zero] at owner
  · simp at h

/-- A control resize asks the pty for the size it gives, clamped, and only a real one. -/
theorem controlResize_source (s : State) (c : Client) (cols rows ec er : UInt32)
    (h : Effect.resizePty ec er ∈ (controlResize s c cols rows).2) :
    cols ≠ 0 ∧
      rows ≠ 0 ∧ ec.toNat = Vt.clampDim cols.toNat ∧ er.toNat = Vt.clampDim rows.toNat := by
  unfold controlResize at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i real
      dsimp only at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨hc, hr⟩ := resize_source s cols rows ec er h
        refine ⟨fun zero => ?_, fun zero => ?_, hc, hr⟩ <;> simp [zero] at real
      · simp at h

/-- **Every pty resize a message asks for is a real size it gives, clamped**: only an attach or a
resize asks for one, and only with no zero in its size. -/
theorem onMsg_resizePty_source (s : State) (c : Client) (m : Msg) (ec er : UInt32)
    (h : Effect.resizePty ec er ∈ (onMsg s c m).2) :
    ∃ mode width height,
      (m = .attach mode width height ∨ m = .resize width height) ∧
        width ≠ 0 ∧
        height ≠ 0 ∧ ec.toNat = Vt.clampDim width.toNat ∧ er.toNat = Vt.clampDim height.toNat := by
  cases m with
  | attach mode cols
    rows =>
    let c' : Client :=
      { c with
        attached := true, mode, seq := s.attachSeq, cols, rows }
    let s1 : State :=
      { s.setClient c' with
        attachSeq := s.attachSeq + 1, lookSeq := s.outSeq, asking := false, notice := none,
        finished := none }
    revert h
    unfold onMsg
    dsimp only
    cases ha : c.attached
    · simp only [Bool.false_eq_true, ↓reduceIte]
      show
        Effect.resizePty ec er ∈
            (resizeOwned s1 c').2 ++
              focusEffects (mode == .writable) s.focused (resizeOwned s1 c').1 ++
              _ ++
              _ →
          _
      intro h
      simp only [List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · obtain ⟨hc, hr, hec, her⟩ := resizeOwned_source s1 c' ec er h
        exact ⟨mode, cols, rows, .inl rfl, hc, hr, hec, her⟩
      · unfold focusEffects at h
        split at h <;> simp at h
      · simp at h
      · split at h <;> simp at h
    · simp
  | resize cols rows =>
    revert h
    unfold onMsg
    dsimp only
    split
    · intro h
      obtain ⟨hc, hr, hec, her⟩ := resizeOwned_source _ _ ec er h
      exact ⟨.writable, cols, rows, .inr rfl, hc, hr, hec, her⟩
    · split
      · simp
      · intro h
        obtain ⟨hc, hr, hec, her⟩ := controlResize_source _ _ cols rows ec er h
        exact ⟨.writable, cols, rows, .inr rfl, hc, hr, hec, her⟩
  | _ =>
    revert h
    unfold onMsg outputMsgs
    dsimp only
    repeat' split
    all_goals simp

/-- An ending asks for no pty resize. -/
theorem conclude_no_resize (s : State) (ending : Ending) (keep : Bool) (cols rows : UInt32) :
    Effect.resizePty cols rows ∉ (conclude s ending keep).2 := by
  obtain ⟨front, effects, only, -⟩ := conclude_shape s ending keep
  rw [effects]
  intro h
  rcases List.mem_append.mp h with h | h
  · exact (front_quiet only).2.2.2.2 cols rows h
  · cases keep <;> simp at h

/-- Only a read asks for a pty resize, and each is a real size an attach or a resize in it gives,
clamped. -/
theorem step_resizePty_source (s : State) (ev : Event) (cols rows : UInt32)
    (resized : Effect.resizePty cols rows ∈ (step s ev).2) :
    ∃ id chunk c,
      ev = .bytes id chunk ∧
        s.client? id = some c ∧
        ∃ m ∈ (c.decoder.feed chunk).2,
          ∃ mode width height,
            (m = .attach mode width height ∨ m = .resize width height) ∧
              width ≠ 0 ∧
              height ≠ 0 ∧
              cols.toNat = Vt.clampDim width.toNat ∧ rows.toNat = Vt.clampDim height.toNat := by
  cases ev with
  | bytes id chunk =>
    cases hc : s.client? id with
    | none => simp [step, hc] at resized
    | some c =>
      refine ⟨id, chunk, c, rfl, hc, ?_⟩
      revert resized
      simp only [step, hc]
      split
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h
        · rcases closed_effects s id _ (by simpa only [step] using h) with h | h <;> cases h
      · intro h
        exact
          feedMsgs_induct _ _ _ (P := fun acc =>
            Effect.resizePty cols rows ∈ acc.2 →
              ∃ m ∈ (c.decoder.feed chunk).2,
                ∃ mode width height,
                  (m = .attach mode width height ∨ m = .resize width height) ∧
                    width ≠ 0 ∧
                    height ≠ 0 ∧
                    cols.toNat = Vt.clampDim width.toNat ∧ rows.toNat = Vt.clampDim height.toNat)
            (fun acc c' m hm _ _ _ hacc h => by
              rcases List.mem_append.mp h with h | h
              · exact hacc h
              · exact ⟨m, hm, onMsg_resizePty_source acc.1 c' m cols rows h⟩)
            (by simp) h
  | connected id =>
    simp only [step] at resized
    split at resized <;> simp at resized
  | closed id => rcases closed_effects s id _ resized with h | h <;> cases h
  | ptyOut chunk =>
    rw [step_ptyOut_effects] at resized
    dsimp only at resized
    rcases List.mem_append.mp resized with h | h
    · split at h <;> simp at h
    · obtain ⟨_, _, he⟩ := broadcast_sends _ _ _ h
      cases he
  | childExited o => exact absurd resized (conclude_no_resize s (.program o) _ cols rows)
  | stopped o => exact absurd resized (conclude_no_resize s (.program o) false cols rows)
  | signal n =>
    rw [step_signal_effects] at resized
    rcases List.mem_cons.mp resized with h | h
    · cases h
    · exact absurd h (conclude_no_resize s (.saved n) true cols rows)
  | tick now =>
    simp only [step] at resized
    split at resized <;> simp at resized
  | checkpointFailed => simp [checkpointFailed_effects] at resized
  | observed o => simp [step] at resized

/-- **No pty resize has a zero dimension**: whatever event arrives, every resize the session asks
for has positive dimensions, and is the size, clamped, of an attach or resize in the read that
asked for it, a size with no zero, so a terminal with no size yet never reaches the pty. -/
theorem step_resizes_sized (s : State) (ev : Event) (cols rows : UInt32)
    (resized : Effect.resizePty cols rows ∈ (step s ev).2) :
    0 < cols ∧
      0 < rows ∧
      ∃ id chunk c,
        ev = .bytes id chunk ∧
          s.client? id = some c ∧
          ∃ m ∈ (c.decoder.feed chunk).2,
            ∃ mode width height,
              (m = .attach mode width height ∨ m = .resize width height) ∧
                width ≠ 0 ∧
                height ≠ 0 ∧
                cols.toNat = Vt.clampDim width.toNat ∧ rows.toNat = Vt.clampDim height.toNat := by
  have source := step_resizePty_source s ev cols rows resized
  have sized : 0 < cols ∧ 0 < rows := by
    obtain ⟨_, _, _, _, _, _, _, _, width, height, _, _, _, hcols, hrows⟩ := source
    have lc := (Vt.clampDim_range width.toNat).1
    have lr := (Vt.clampDim_range height.toNat).1
    constructor <;> rw [UInt32.lt_iff_toNat_lt] <;> simp only [UInt32.toNat_zero] <;> omega
  exact ⟨sized.1, sized.2, source⟩

/-- A booted session's first connection, once it attached writable at 80×24, holds that record:
the witness the kill of a resize that drops typing starts from. -/
theorem attached_client_witness :
    (trace step (State.boot (Vt.Vt.init 1 1) [] [])
            [.connected 1, .bytes 1 (Wire.encode (.attach .writable 80 24))]).1.client?
        1 =
      some { id := 1, attached := true, cols := 80, rows := 24 } := by
  change
    (step (trace step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1
            (.bytes 1 (Wire.encode (.attach .writable 80 24)))).1.client?
        1 =
      _
  rw [step_attach_record connected_client_witness.1 rfl (feed_encode_fresh _ trivial) rfl]
  rfl

/-- In that session the connection is attached and the scanner idle, so a plain byte of program
output is released as it is: the witness the kill of a step that drops output starts from. -/
theorem attached_output_witness :
    let s :=
      (trace step (State.boot (Vt.Vt.init 1 1) [] [])
          [.connected 1, .bytes 1 (Wire.encode (.attach .writable 80 24))]).1
    (∃ c ∈ s.roster, c.attached = true) ∧
      (Mediation.feed s.terminal s.scanner [0x41]).visible = [0x41] := by
  intro s
  refine ⟨⟨_, client?_mem attached_client_witness, rfl⟩, ?_⟩
  have hscan : s.scanner = .ground := by
    change
      (step (trace step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1
            (.bytes 1 (Wire.encode (.attach .writable 80 24)))).1.scan =
        .ground
    rw [step_bytes_single connected_client_witness.1
        (feed_encode_fresh (.attach .writable 80 24) trivial) rfl,
      onMsg_scan]
    rfl
  rw [hscan]
  simp [Mediation.feed, Mediation.Scan.step, Mediation.ESC]

/-! ## How a session's processes end -/

/-- A daemon ends its program and the rest of the program's terminal session with SIGHUP, then
SIGKILL a second later, and waits a second more for SIGKILL. -/
theorem ending_eq : ending = [(1, 1000), (9, 1000)] := rfl

/-! ## Work follows events -/

/-- A daemon's poll sleeps until the earliest deadline it holds, at once for one already past,
and for an event however long that takes, `-1`, when it holds none. -/
theorem pollTimeout_eq (now : Nat) (deadlines : List Nat) :
    pollTimeout now deadlines =
      (deadlines.min?.map fun due => Int32.ofNat (min (due - now) 2147483647)).getD (-1) := rfl

/-- While a write runs, a write asked for waits, in place of any that waited. -/
theorem run_ask_running {R W : Type} (start : W → R) (o : Offloop R W) (w : W)
    (h : o.running.isSome = true) :
    Offloop.run Offloop.ask start o w = { o with waiting := some w } := by
  simp [Offloop.run, Offloop.ask, h]

/-- While a write runs, the writes asked for leave it running and the last of them waiting. -/
theorem foldl_ask_running {R W : Type} (start : W → R) (o : Offloop R W)
    (h : o.running.isSome = true) (ws : List W) :
    (ws.foldl (Offloop.run Offloop.ask start) o).running = o.running ∧
      (ws.foldl (Offloop.run Offloop.ask start) o).waiting =
        ws.getLast?.orElse fun _ => o.waiting := by
  induction ws generalizing o with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons]
    rw [run_ask_running start o w h]
    have rest := ih { o with waiting := some w } h
    refine ⟨rest.1, ?_⟩
    rw [rest.2]
    cases ws with
    | nil => simp
    | cons x xs => simp [List.getLast?_cons]

/-- **Off-loop writes never queue**: of the writes a daemon asks for while none ends, the first
runs and only the last waits. -/
theorem offloop_coalesces {R W : Type} (start : W → R) (ws : List W) :
    (ws.foldl (Offloop.run Offloop.ask start) {}).running = ws.head?.map start ∧
      (ws.foldl (Offloop.run Offloop.ask start) {}).waiting =
        if ws.length ≤ 1 then none else ws.getLast? := by
  cases ws with
  | nil => simp
  | cons w ws =>
    simp only [List.foldl_cons]
    have first : Offloop.run Offloop.ask start {} w = { running := some (start w) } := by
      simp [Offloop.run, Offloop.ask]
    rw [first]
    have rest := foldl_ask_running start { running := some (start w) } rfl ws
    refine ⟨by simpa using rest.1, ?_⟩
    rw [rest.2]
    cases ws with
    | nil => simp
    | cons x xs => simp [List.getLast?_cons]

/-! ## What a crash costs

What a save holds of a session is its terminal and its labels. Every change to either marks the
session unsaved; only a step that asks for a save clears the mark, and only a periodic save moves
the save clock, to its tick's time. So once a session holds a change no save holds, a save falls
due within `ckptIntervalMs` of the clock at that change, and the session wakes for it. -/

/-- A message keeps the save clock and never clears the unsaved mark. -/
theorem onMsg_unsaved_kept (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).1.lastCkptMs = s.lastCkptMs ∧
      (s.dirty = true → (onMsg s c m).1.dirty = true) := by
  unfold onMsg
  grind

/-- A message that changes the terminal marks the session unsaved. -/
theorem onMsg_vt_changed_dirty (s : State) (c : Client) (m : Msg) (h : (onMsg s c m).1.vt ≠ s.vt) :
    (onMsg s c m).1.dirty = true := by
  unfold onMsg at *
  grind

/-- A batch of messages keeps the save clock and never clears the unsaved mark, and one that
changes the terminal or the labels marks the session unsaved. -/
theorem feedMsgs_unsaved (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan)) :
    (feedMsgs id msgs acc).1.lastCkptMs = acc.1.lastCkptMs ∧
      ((feedMsgs id msgs acc).1.dirty = true ∨
        acc.1.dirty = false ∧
          (feedMsgs id msgs acc).1.vt = acc.1.vt ∧
          (feedMsgs id msgs acc).1.fields = acc.1.fields) := by
  apply
    feedMsgs_preserves id msgs acc (P := fun t =>
      t.lastCkptMs = acc.1.lastCkptMs ∧
        (t.dirty = true ∨ acc.1.dirty = false ∧ t.vt = acc.1.vt ∧ t.fields = acc.1.fields))
  · intro t c m _ ⟨clock, mark⟩
    obtain ⟨kept, mono⟩ := onMsg_unsaved_kept t c m
    refine ⟨kept.trans clock, ?_⟩
    rcases mark with dirty | ⟨clean, vt, labels⟩
    · exact .inl (mono dirty)
    · by_cases hv : (onMsg t c m).1.vt = t.vt
      · by_cases hl : (onMsg t c m).1.fields = t.fields
        · cases hd : (onMsg t c m).1.dirty
          · exact .inr ⟨clean, hv.trans vt, hl.trans labels⟩
          · exact .inl rfl
        · exact .inl (onMsg_labels_changed_dirty t c m hl)
      · exact .inl (onMsg_vt_changed_dirty t c m hv)
  · cases hd : acc.1.dirty
    · exact ⟨rfl, .inr ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨rfl, .inl rfl⟩

/-- An event that changes what a save holds, the terminal or the labels, marks the session
unsaved. -/
theorem step_changed_dirty (s : State) (ev : Event)
    (h : (step s ev).1.vt ≠ s.vt ∨ (step s ev).1.fields ≠ s.fields) :
    (step s ev).1.dirty = true := by
  cases ev with
  | ptyOut chunk => rfl
  | checkpointFailed => rfl
  | observed o => simp [step] at h
  | connected id =>
    simp only [step] at h ⊢
    split at h <;> simp_all
  | closed id =>
    simp only [step, closeClient_vt, closeClient_labels] at h
    simp at h
  | childExited o =>
    simp only [step, conclude] at h
    simp at h
  | stopped o =>
    simp only [step, conclude] at h
    simp at h
  | signal n =>
    simp only [step, conclude] at h
    simp at h
  | tick now =>
    simp only [step] at h
    split at h <;> simp [State.ticked] at h
  | bytes id chunk =>
    simp only [step] at h ⊢
    split at h
    · simp at h
    · rename_i c _
      split at h
      · simp [closeClient_vt, closeClient_labels] at h
      · rename_i hok
        simp only [hok] at ⊢
        rcases
          (feedMsgs_unsaved id (c.decoder.feed chunk).2
              (s.setClient
                  { c with
                    decoder := (c.decoder.feed chunk).1, answered := false },
                [])).2 with
          dirty | ⟨-, vt, labels⟩
        · exact dirty
        · simp only [State.setClient] at vt labels
          rcases h with h | h
          · exact absurd vt h
          · exact absurd labels h

/-- A step that asks for no save keeps the save clock and does not clear the unsaved mark. -/
theorem step_unsaved_kept (s : State) (ev : Event) (h : Effect.checkpoint ∉ (step s ev).2) :
    (step s ev).1.lastCkptMs = s.lastCkptMs ∧ (s.dirty = true → (step s ev).1.dirty = true) := by
  cases ev with
  | ptyOut chunk => exact ⟨rfl, fun _ => rfl⟩
  | checkpointFailed => exact ⟨rfl, fun _ => rfl⟩
  | observed o => exact ⟨rfl, fun d => d⟩
  | connected i =>
    simp only [step]
    split <;> exact ⟨rfl, fun d => d⟩
  | childExited o => exact ⟨rfl, fun d => d⟩
  | stopped o => exact ⟨rfl, fun d => d⟩
  | signal n => exact ⟨rfl, fun d => d⟩
  | tick now =>
    simp only [step] at h ⊢
    split <;> simp_all [State.ticked]
  | closed i =>
    simp only [step, closeClient] at h ⊢
    split <;> simp_all [State.dropClient]
  | bytes i chunk =>
    simp only [step] at h ⊢
    split
    · exact ⟨rfl, fun d => d⟩
    · rename_i c _
      split
      · simp only [closeClient] at h ⊢
        split <;> simp_all [State.dropClient]
      · rename_i hok
        obtain ⟨clock, mark⟩ :=
          feedMsgs_unsaved i (c.decoder.feed chunk).2
            (s.setClient
                { c with
                  decoder := (c.decoder.feed chunk).1, answered := false },
              [])
        refine ⟨clock, fun dirty => ?_⟩
        rcases mark with marked | ⟨clean, -⟩
        · exact marked
        · simp [State.setClient, dirty] at clean

/-- Only a periodic save moves the save clock, to its tick's time. -/
theorem step_lastCkptMs (s : State) (ev : Event) :
    (step s ev).1.lastCkptMs = s.lastCkptMs ∨
      ∃ now, ev = .tick now ∧ (step s ev).1.lastCkptMs = now := by
  cases ev with
  | tick now =>
    simp only [step]
    split
    · exact .inr ⟨now, rfl, rfl⟩
    · exact .inl rfl
  | connected i =>
    left
    simp only [step]
    split <;> rfl
  | closed i =>
    left
    simp only [step, closeClient]
    split <;> rfl
  | bytes i chunk =>
    left
    simp only [step]
    split
    · rfl
    · split
      · simp only [closeClient]
        split <;> rfl
      · exact (feedMsgs_unsaved i _ _).1
  | ptyOut chunk => exact .inl rfl
  | childExited o => exact .inl rfl
  | stopped o => exact .inl rfl
  | signal n => exact .inl rfl
  | checkpointFailed => exact .inl rfl
  | observed o => exact .inl rfl

/-- The save clock is the boot's or a tick's time: never later than the clock the events give. -/
theorem trace_lastCkptMs_le (s : State) (evs : List Event) :
    (trace step s evs).1.lastCkptMs ≤ max s.lastCkptMs (clock evs) := by
  induction evs generalizing s with
  | nil => exact Nat.le_max_left _ _
  | cons ev evs ih =>
    have next := ih (step s ev).1
    simp only [trace]
    have tail : clock evs ≤ clock (ev :: evs) := by cases ev <;> simp [clock, Nat.le_max_right]
    rcases step_lastCkptMs s ev with kept | ⟨now, rfl, moved⟩
    · rw [kept] at next
      omega
    · rw [moved] at next
      simp only [clock] at tail ⊢
      omega

/-- A booted session's save clock is never later than the clock its events give. -/
theorem boot_lastCkptMs_le (vt : Vt.Vt) (labels metaKv : List (String × String))
    (evs : List Event) :
    (trace step (State.boot vt labels metaKv) evs).1.lastCkptMs ≤ clock evs := by
  have := trace_lastCkptMs_le (State.boot vt labels metaKv) evs
  simpa [State.boot] using this

/-- A trace that asks for no save keeps the save clock and does not clear the unsaved mark. -/
theorem trace_unsaved_kept (s : State) (evs : List Event)
    (h : Effect.checkpoint ∉ (trace step s evs).2) :
    (trace step s evs).1.lastCkptMs = s.lastCkptMs ∧
      (s.dirty = true → (trace step s evs).1.dirty = true) := by
  induction evs generalizing s with
  | nil => exact ⟨rfl, id⟩
  | cons ev evs ih =>
    simp only [trace, List.mem_append, not_or] at h ⊢
    obtain ⟨first, rest⟩ := h
    obtain ⟨clock, mark⟩ := step_unsaved_kept s ev first
    obtain ⟨clock', mark'⟩ := ih (step s ev).1 rest
    exact ⟨clock'.trans clock, fun dirty => mark' (mark dirty)⟩

/-- **A change no save holds falls due within the interval.** Once an event changes what a save
holds and no step since asked for a save, the session's save falls due no later than
`ckptIntervalMs` after any time no earlier than the save clock before that change, the session
wakes no later than that, and a tick then asks for the save. -/
theorem unsaved_due (s : State) (ev : Event) (post : List Event) {t : Nat}
    (clocked : s.lastCkptMs ≤ t)
    (changed : (step s ev).1.vt ≠ s.vt ∨ (step s ev).1.fields ≠ s.fields)
    (unsaved : Effect.checkpoint ∉ (trace step s (ev :: post)).2) :
    ∃ due,
      due ≤ t + ckptIntervalMs ∧
        (∃ wake, (trace step s (ev :: post)).1.nextTick = some wake ∧ wake ≤ due) ∧
        ∀ now,
          due ≤ now → Effect.checkpoint ∈ (step (trace step s (ev :: post)).1 (.tick now)).2 := by
  obtain ⟨kept, -⟩ := trace_unsaved_kept s (ev :: post) unsaved
  simp only [trace, List.mem_append, not_or] at unsaved kept ⊢
  have marked :=
    (trace_unsaved_kept (step s ev).1 post unsaved.2).2 (step_changed_dirty s ev changed)
  refine
    ⟨(trace step (step s ev).1 post).1.lastCkptMs + ckptIntervalMs, by omega,
      nextTick_save _ marked, fun now due => ?_⟩
  rw [(step_tick_checkpoint _ now
        (by
          simp [marked]; omega)).1]
  exact List.mem_singleton.mpr rfl

/-! ## Asking for someone

`asking` is "the program rang the bell or posted a notification since the session was last
looked at", a property of the session, as `unseen` is: output with nobody attached raises it as
the mediator hears it, every look — an attach, a capture, output while a client is attached —
clears it, and no other event changes it. The last notification's text since then, `notice`,
follows it: raised with it, cleared with it, and within the OSC buffer's cap. -/

/-- A bell from ground asks, whatever the terminal: the fact a kill needs of the mediator. -/
theorem feed_bel_asks (v : Terminal.Vt.Vt) :
    (Terminal.Mediation.feed v .ground [0x07]).asks = true :=
  Terminal.Mediation.feed_bell v [] [] (by simp)

/-- **Output asks as it is heard**: output with nobody attached asks when it rang the bell or
posted a notification, or when the session asked already; output while a client is attached is
seen as it arrives, and asks nothing. -/
theorem step_ptyOut_asking (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.seen.asks =
      (!seenBy s.roster &&
        ((Terminal.Mediation.feed s.terminal s.scanner chunk).asks || s.seen.asks)) := by
  simp only [step, State.seen, seenBy, State.roster, State.terminal, State.scanner]
  cases s.clients.any (·.attached) <;> simp [Bool.or_comm]

/-- Resizing on behalf of the size owner leaves the ask and its text alone. -/
theorem resizeOwned_asking (s : State) (c : Client) :
    (resizeOwned s c).1.asking = s.asking ∧ (resizeOwned s c).1.notice = s.notice := by
  unfold resizeOwned resize
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- **A look clears the ask**: an attach from a connection not yet attached, or a capture, read
alone from a healthy decoder, leaves the session asking nothing, and no notification's text. -/
theorem step_look_clears (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {m : Msg} (hc : s.client? id = some c) (fresh : c.attached = false)
    (read : c.decoder.feed chunk = (dec, [m])) (healthy : dec.errored = false) (looks : m.Looks) :
    (step s (.bytes id chunk)).1.seen.asks = false ∧
      (step s (.bytes id chunk)).1.notice = none := by
  rw [step_bytes_single hc read healthy]
  cases m <;> simp only [Msg.Looks] at looks
  · unfold onMsg
    simp only [fresh, Bool.false_eq_true, ↓reduceIte, State.seen]
    exact ⟨(resizeOwned_asking _ _).1, (resizeOwned_asking _ _).2⟩
  · rw [onMsg_screen _ _ rfl]
    exact ⟨rfl, rfl⟩

/-- A message that is no look leaves the ask and its text as they were. -/
theorem onMsg_asking_kept (s : State) (c : Client) (m : Msg) (h : ¬m.Looks) :
    (onMsg s c m).1.asking = s.asking ∧ (onMsg s c m).1.notice = s.notice := by
  cases m
  all_goals simp only [Msg.Looks, not_true_eq_false] at h
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- Every message leaves the ask and its text as they were, or clears both. -/
theorem onMsg_asking (s : State) (c : Client) (m : Msg) :
    ((onMsg s c m).1.asking = s.asking ∧ (onMsg s c m).1.notice = s.notice) ∨
      ((onMsg s c m).1.asking = false ∧ (onMsg s c m).1.notice = none) := by
  cases m
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- No message raises an ask: a look clears it, and any other leaves it. -/
theorem onMsg_asking_le (s : State) (c : Client) (m : Msg) (h : (onMsg s c m).1.asking = true) :
    s.asking = true := by
  rcases onMsg_asking s c m with ⟨ha, -⟩ | ⟨ha, -⟩
  · rwa [ha] at h
  · rw [ha] at h
    exact absurd h (by decide)

/-- …nor posts a notification's text. -/
theorem onMsg_notice_le (s : State) (c : Client) (m : Msg) (text : List UInt8)
    (h : (onMsg s c m).1.notice = some text) : s.notice = some text := by
  rcases onMsg_asking s c m with ⟨-, hn⟩ | ⟨-, hn⟩
  · rwa [hn] at h
  · rw [hn] at h
    cases h

/-- No batch of messages raises an ask. -/
theorem feedMsgs_asking_le (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (h : (feedMsgs id msgs acc).1.asking = true) : acc.1.asking = true :=
  feedMsgs_induct id msgs acc (P := fun r => r.1.asking = true → acc.1.asking = true)
    (fun current c m _ _ _ _ hs hr => hs (onMsg_asking_le current.1 c m hr)) (fun h => h) h

/-- …nor posts a notification's text. -/
theorem feedMsgs_notice_le (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (text : List UInt8) (h : (feedMsgs id msgs acc).1.notice = some text) :
    acc.1.notice = some text :=
  feedMsgs_induct id msgs acc (P := fun r => r.1.notice = some text → acc.1.notice = some text)
    (fun current c m _ _ _ _ hs hr => hs (onMsg_notice_le current.1 c m text hr)) (fun h => h) h

/-- What a read changes of the session it reaches through no message: closing an errored peer,
or ignoring a peer the session no longer holds, keeps the ask and its text. -/
theorem step_bytes_cases (s : State) (id : Nat) (chunk : List UInt8) :
    ((step s (.bytes id chunk)).1.asking = s.asking ∧
        (step s (.bytes id chunk)).1.notice = s.notice) ∨
      ∃ c,
        s.client? id = some c ∧
          (c.decoder.feed chunk).1.errored = false ∧
          (step s (.bytes id chunk)).1 =
            (feedMsgs id (c.decoder.feed chunk).2
                (s.setClient
                    { c with
                      decoder := (c.decoder.feed chunk).1, answered := false },
                  [])).1 := by
  unfold step
  dsimp only
  split
  · exact .inl ⟨rfl, rfl⟩
  · rename_i c hc
    split
    · left
      unfold closeClient
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
    · rename_i hok
      exact .inr ⟨c, hc, by simpa using hok, rfl⟩

/-- **Only output raises an ask**: an event after which the session asks is output, or the session
asked already. -/
theorem step_asking_raised (s : State) (ev : Event) (h : (step s ev).1.seen.asks = true) :
    s.seen.asks = true ∨ ∃ chunk, ev = .ptyOut chunk := by
  simp only [State.seen] at h ⊢
  cases ev with
  | ptyOut chunk => exact .inr ⟨chunk, rfl⟩
  | bytes id chunk =>
    left
    rcases step_bytes_cases s id chunk with ⟨ha, -⟩ | ⟨c, -, -, heq⟩
    · rwa [ha] at h
    · rw [heq] at h
      simpa [State.setClient] using feedMsgs_asking_le id _ _ h
  | closed id =>
    left
    revert h
    unfold step closeClient
    dsimp only
    split <;> exact fun h => h
  | connected id =>
    left
    revert h
    unfold step
    dsimp only
    split <;> exact fun h => h
  | childExited o => exact .inl h
  | stopped o => exact .inl h
  | signal n => exact .inl h
  | tick now =>
    left
    revert h
    unfold step
    dsimp only
    split <;> exact fun h => h
  | observed o => exact .inl h
  | checkpointFailed => exact .inl h

/-- A batch with no look leaves the ask and its text as they were. -/
theorem feedMsgs_asking (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (none : ∀ m ∈ msgs, ¬m.Looks) : (feedMsgs id msgs acc).1.asking = acc.1.asking := by
  exact
    feedMsgs_induct id msgs acc (P := fun r => r.1.asking = acc.1.asking)
      (fun current c m hm _ _ _ hs => (onMsg_asking_kept current.1 c m (none m hm)).1.trans hs) rfl

/-- **Only a look clears an ask**: an event after which a session that asked asks no longer is
output, which a client attached saw, or a read, from a connection the session holds, that holds
an attach or a capture. -/
theorem step_asking_cleared (s : State) (ev : Event) (was : s.seen.asks = true)
    (cleared : (step s ev).1.seen.asks = false) :
    (∃ chunk, ev = .ptyOut chunk) ∨
      ∃ id chunk c,
        ev = .bytes id chunk ∧ s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks := by
  simp only [State.seen] at was cleared
  have kept : (step s ev).1.asking = s.asking → False := fun h => by simp_all
  cases ev with
  | ptyOut chunk => exact .inl ⟨chunk, rfl⟩
  | bytes id chunk =>
    right
    cases hc : s.client? id with
    | none => exact absurd (by simp [step, hc]) kept
    | some c =>
      refine ⟨id, chunk, c, rfl, hc, ?_⟩
      apply Classical.byContradiction
      intro hnone
      apply kept
      simp only [not_exists, not_and] at hnone
      simp only [step, hc]
      split
      · unfold closeClient
        dsimp only
        split <;> rfl
      · rw [feedMsgs_asking]
        · simp [State.setClient]
        · exact fun m hm => hnone m hm
  | closed id =>
    refine absurd ?_ kept
    unfold step closeClient
    dsimp only
    split <;> rfl
  | connected id =>
    refine absurd ?_ kept
    dsimp only [step]
    split <;> rfl
  | childExited o => exact absurd rfl kept
  | stopped o => exact absurd rfl kept
  | signal n => exact absurd rfl kept
  | tick now =>
    refine absurd ?_ kept
    dsimp only [step]
    split <;> rfl
  | observed o => exact absurd rfl kept
  | checkpointFailed => exact absurd rfl kept

/-- **A notification's text is bounded**: from a state whose scanner is within its caps and whose
notification's text fits the OSC buffer's cap, every event leaves a text that fits it. -/
theorem step_notice_le (s : State) (ev : Event) (hs : s.scan.Bounded)
    (hn : ∀ text, s.notice = some text → text.length ≤ Terminal.Mediation.oscCap) :
    ∀ text, (step s ev).1.notice = some text → text.length ≤ Terminal.Mediation.oscCap := by
  cases ev with
  | ptyOut chunk =>
    intro text h
    simp only [step] at h
    split at h
    · simp at h
    · cases hr : (Terminal.Mediation.feed s.vt s.scan chunk).notice with
      | some t =>
        rw [hr, Option.some_or] at h
        cases h
        exact Terminal.Mediation.feed_notice_le s.vt s.scan chunk hs _ hr
      | none =>
        rw [hr, Option.none_or] at h
        exact hn text h
  | bytes id chunk =>
    intro text h
    rcases step_bytes_cases s id chunk with ⟨-, hkept⟩ | ⟨c, -, -, heq⟩
    · rw [hkept] at h
      exact hn text h
    · rw [heq] at h
      exact hn text (by simpa [State.setClient] using feedMsgs_notice_le id _ _ text h)
  | closed id =>
    unfold step closeClient
    dsimp only
    split <;> exact hn
  | connected id =>
    dsimp only [step]
    split <;> exact hn
  | childExited o => exact hn
  | stopped o => exact hn
  | signal n => exact hn
  | tick now =>
    dsimp only [step]
    split <;> exact hn
  | observed o => exact hn
  | checkpointFailed => exact hn

/-! ## A shell's commands

`running` and `finished` are what the session heard of its shell's commands, from the marks the
mediator hears, each as `Commands.hear` says it tells. The ending is told until seen, as an ask
is: output with nobody attached sets it as its marks tell, every look clears it, and no other
event changes it; the running command changes only with output. Both command lines stay within
the OSC buffer's cap. -/

/-- A `C` mark alone, ended by BEL, from ground, is heard as a command that runs with no command
line given, whatever the terminal: the fact a kill needs of the mediator. -/
theorem feed_mark_runs (v : Terminal.Vt.Vt) :
    (Terminal.Mediation.feed v .ground [0x1B, 0x5D, 0x31, 0x33, 0x33, 0x3B, 0x43, 0x07]).marks =
      [.runs {}] :=
  Terminal.Mediation.feed_osc_mark v [0x31, 0x33, 0x33, 0x3B, 0x43]
    (by
      unfold Terminal.Mediation.Plain; decide)
    (by decide) [0x07] (.inl rfl)

/-- What the session hears in a mark is what `Commands.hear` says the mark tells. -/
theorem hearMark_hear (c : Commands) (m : Terminal.Mediation.Mark) :
    hearMark (c.running, c.finished) m = ((c.hear m).running, (c.hear m).finished) := by
  cases m with
  | finished status => cases h : c.running <;> simp [hearMark, Commands.hear, h]
  | _ => rfl

/-- …and so in every mark of a chunk, in order. -/
theorem foldl_hearMark (marks : List Terminal.Mediation.Mark) (c : Commands) :
    marks.foldl hearMark (c.running, c.finished) =
      ((marks.foldl Commands.hear c).running, (marks.foldl Commands.hear c).finished) := by
  induction marks generalizing c with
  | nil => rfl
  | cons m ms ih => simp only [List.foldl_cons, hearMark_hear, ih]

/-- **Output tells the commands as its marks do**: output hears each of its marks as
`Commands.hear` says it tells, and an ending in output an attached client saw is seen as it
arrives. -/
theorem step_ptyOut_commands (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.commands.running =
        ((Terminal.Mediation.feed s.terminal s.scanner chunk).marks.foldl Commands.hear
            s.commands).running ∧
      (step s (.ptyOut chunk)).1.commands.finished =
        if seenBy s.roster then none
        else
          ((Terminal.Mediation.feed s.terminal s.scanner chunk).marks.foldl Commands.hear
              s.commands).finished := by
  have h := foldl_hearMark (Terminal.Mediation.feed s.vt s.scan chunk).marks s.commands
  simp only [State.commands] at h
  constructor
  · simp only [step, State.commands, State.terminal, State.scanner, h]
  · simp only [step, State.commands, seenBy, State.roster, State.terminal, State.scanner, h]
    rfl

/-- Resizing on behalf of the size owner leaves the commands alone. -/
theorem resizeOwned_commands (s : State) (c : Client) :
    (resizeOwned s c).1.running = s.running ∧ (resizeOwned s c).1.finished = s.finished := by
  unfold resizeOwned resize
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- **A look clears the ending**: an attach from a connection not yet attached, or a capture, read
alone from a healthy decoder, leaves no ending to tell, and the running command as it was. -/
theorem step_look_clears_finished (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {m : Msg} (hc : s.client? id = some c) (fresh : c.attached = false)
    (read : c.decoder.feed chunk = (dec, [m])) (healthy : dec.errored = false) (looks : m.Looks) :
    (step s (.bytes id chunk)).1.commands.finished = none ∧
      (step s (.bytes id chunk)).1.commands.running = s.commands.running := by
  rw [step_bytes_single hc read healthy]
  cases m <;> simp only [Msg.Looks] at looks
  · unfold onMsg
    simp only [fresh, Bool.false_eq_true, ↓reduceIte, State.commands]
    exact ⟨(resizeOwned_commands _ _).2, (resizeOwned_commands _ _).1⟩
  · rw [onMsg_screen _ _ rfl]
    exact ⟨rfl, rfl⟩

/-- A message that is no look leaves the commands as they were. -/
theorem onMsg_commands_kept (s : State) (c : Client) (m : Msg) (h : ¬m.Looks) :
    (onMsg s c m).1.running = s.running ∧ (onMsg s c m).1.finished = s.finished := by
  cases m
  all_goals simp only [Msg.Looks, not_true_eq_false] at h
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- Every message leaves the running command as it was, and the ending as it was or cleared. -/
theorem onMsg_commands (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).1.running = s.running ∧
      ((onMsg s c m).1.finished = s.finished ∨ (onMsg s c m).1.finished = none) := by
  cases m
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- No batch of messages changes the running command, nor tells an ending. -/
theorem feedMsgs_commands (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan)) :
    (feedMsgs id msgs acc).1.running = acc.1.running ∧
      ((feedMsgs id msgs acc).1.finished = acc.1.finished ∨
        (feedMsgs id msgs acc).1.finished = none) :=
  feedMsgs_induct id msgs acc (P := fun r =>
    r.1.running = acc.1.running ∧ (r.1.finished = acc.1.finished ∨ r.1.finished = none))
    (fun current c m _ _ _ _ hs => by
      obtain ⟨hr, hf⟩ := onMsg_commands current.1 c m
      refine ⟨hr.trans hs.1, ?_⟩
      rcases hf with hf | hf
      · rw [hf]
        exact hs.2
      · exact .inr hf)
    ⟨rfl, .inl rfl⟩

/-- A batch with no look leaves the ending as it was. -/
theorem feedMsgs_finished (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (none : ∀ m ∈ msgs, ¬m.Looks) : (feedMsgs id msgs acc).1.finished = acc.1.finished :=
  feedMsgs_induct id msgs acc (P := fun r => r.1.finished = acc.1.finished)
    (fun current c m hm _ _ _ hs => (onMsg_commands_kept current.1 c m (none m hm)).2.trans hs) rfl

/-- What a read changes of the commands through no message: closing an errored peer, or ignoring a
peer the session no longer holds, keeps them. -/
theorem step_bytes_commands_cases (s : State) (id : Nat) (chunk : List UInt8) :
    ((step s (.bytes id chunk)).1.running = s.running ∧
        (step s (.bytes id chunk)).1.finished = s.finished) ∨
      ∃ c,
        s.client? id = some c ∧
          (c.decoder.feed chunk).1.errored = false ∧
          (step s (.bytes id chunk)).1 =
            (feedMsgs id (c.decoder.feed chunk).2
                (s.setClient
                    { c with
                      decoder := (c.decoder.feed chunk).1, answered := false },
                  [])).1 := by
  unfold step
  dsimp only
  split
  · exact .inl ⟨rfl, rfl⟩
  · rename_i c hc
    split
    · left
      unfold closeClient
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
    · rename_i hok
      exact .inr ⟨c, hc, by simpa using hok, rfl⟩

/-- **Only output changes the running command.** -/
theorem step_running_kept (s : State) (ev : Event) (h : ∀ chunk, ev ≠ .ptyOut chunk) :
    (step s ev).1.commands.running = s.commands.running := by
  simp only [State.commands]
  cases ev with
  | ptyOut chunk => exact absurd rfl (h chunk)
  | bytes id
    chunk =>
    rcases step_bytes_commands_cases s id chunk with ⟨hr, -⟩ | ⟨c, -, -, heq⟩
    · exact hr
    · rw [heq]
      simpa [State.setClient] using (feedMsgs_commands id _ _).1
  | closed id =>
    unfold step closeClient
    dsimp only
    split <;> rfl
  | connected id =>
    dsimp only [step]
    split <;> rfl
  | childExited o => rfl
  | stopped o => rfl
  | signal n => rfl
  | tick now =>
    dsimp only [step]
    split <;> rfl
  | observed o => rfl
  | checkpointFailed => rfl

/-- **Only output and looks change the ending, and a look clears it**: an event after which the
ending differs is output, or a read, from a connection the session holds, that holds an attach or
a capture, after which no ending is told. -/
theorem step_finished_changed (s : State) (ev : Event)
    (changed : (step s ev).1.commands.finished ≠ s.commands.finished) :
    (∃ chunk, ev = .ptyOut chunk) ∨
      (step s ev).1.commands.finished = none ∧
        ∃ id chunk c,
          ev = .bytes id chunk ∧
            s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks := by
  simp only [State.commands] at changed ⊢
  cases ev with
  | ptyOut chunk => exact .inl ⟨chunk, rfl⟩
  | bytes id chunk =>
    right
    rcases step_bytes_commands_cases s id chunk with ⟨-, hf⟩ | ⟨c, hc, -, heq⟩
    · exact absurd hf changed
    · rw [heq] at changed ⊢
      refine ⟨?_, id, chunk, c, rfl, hc, ?_⟩
      · rcases
          (feedMsgs_commands id (c.decoder.feed chunk).2
              (s.setClient
                  { c with
                    decoder := (c.decoder.feed chunk).1, answered := false },
                [])).2 with
          hf | hf
        · exact absurd (by simpa [State.setClient] using hf) changed
        · exact hf
      · apply Classical.byContradiction
        intro hnone
        apply changed
        simp only [not_exists, not_and] at hnone
        rw [feedMsgs_finished]
        · simp [State.setClient]
        · exact fun m hm => hnone m hm
  | closed id =>
    refine absurd ?_ changed
    unfold step closeClient
    dsimp only
    split <;> rfl
  | connected id =>
    refine absurd ?_ changed
    dsimp only [step]
    split <;> rfl
  | childExited o => exact absurd rfl changed
  | stopped o => exact absurd rfl changed
  | signal n => exact absurd rfl changed
  | tick now =>
    refine absurd ?_ changed
    dsimp only [step]
    split <;> rfl
  | observed o => exact absurd rfl changed
  | checkpointFailed => exact absurd rfl changed

/-- Hearing marks whose command lines fit the OSC buffer's cap, from commands whose command lines
fit it, leaves command lines that fit it. -/
theorem foldl_hearMark_le (marks : List Terminal.Mediation.Mark)
    (heard : Option Terminal.Mediation.Cmdline × Option Finished)
    (hm : ∀ c, .runs c ∈ marks → c.bytes.length ≤ Terminal.Mediation.oscCap)
    (hr : ∀ c, heard.1 = some c → c.bytes.length ≤ Terminal.Mediation.oscCap)
    (hf : ∀ f, heard.2 = some f → f.cmdline.bytes.length ≤ Terminal.Mediation.oscCap) :
    (∀ c, (marks.foldl hearMark heard).1 = some c → c.bytes.length ≤ Terminal.Mediation.oscCap) ∧
      ∀ f,
        (marks.foldl hearMark heard).2 = some f →
          f.cmdline.bytes.length ≤ Terminal.Mediation.oscCap := by
  induction marks generalizing heard with
  | nil => exact ⟨hr, hf⟩
  | cons m ms ih =>
    simp only [List.foldl_cons]
    apply ih _ (fun c hc => hm c (List.mem_cons_of_mem m hc))
    · cases m with
      | prompt => simp [hearMark]
      | input => exact hr
      | runs cmdline =>
        intro c hc
        simp only [hearMark, Option.some.injEq] at hc
        subst hc
        exact hm cmdline List.mem_cons_self
      | finished status =>
        intro c hc
        cases h : heard.1 with
        | none =>
          simp only [hearMark, h] at hc;
          exact
            hr c
              (by
                rw [h]; exact hc)
        | some d => simp [hearMark, h] at hc
    · cases m with
      | prompt => exact hf
      | input => exact hf
      | runs cmdline => simp [hearMark]
      | finished status =>
        intro f hfin
        cases h : heard.1 with
        | none =>
          simp only [hearMark, h] at hfin; exact hf f hfin
        | some d =>
          simp only [hearMark, h, Option.some.injEq] at hfin
          subst hfin
          exact hr d h

/-- **A command line is bounded**: from a state whose scanner is within its caps and whose command
lines fit the OSC buffer's cap, every event leaves command lines that fit it. -/
theorem step_cmdline_le (s : State) (ev : Event) (hs : s.scan.Bounded)
    (hr : ∀ c, s.running = some c → c.bytes.length ≤ Terminal.Mediation.oscCap)
    (hf : ∀ f, s.finished = some f → f.cmdline.bytes.length ≤ Terminal.Mediation.oscCap) :
    (∀ c, (step s ev).1.running = some c → c.bytes.length ≤ Terminal.Mediation.oscCap) ∧
      ∀ f,
        (step s ev).1.finished = some f → f.cmdline.bytes.length ≤ Terminal.Mediation.oscCap := by
  by_cases hout : ∃ chunk, ev = .ptyOut chunk
  · obtain ⟨chunk, rfl⟩ := hout
    have bounded :=
      foldl_hearMark_le (Terminal.Mediation.feed s.vt s.scan chunk).marks (s.running, s.finished)
        (fun c hc => Terminal.Mediation.feed_cmdline_le s.vt s.scan chunk hs c hc) hr hf
    refine ⟨fun c hc => bounded.1 c hc, fun f hfin => ?_⟩
    simp only [step] at hfin
    split at hfin
    · cases hfin
    · exact bounded.2 f hfin
  · have kept := step_running_kept s ev fun chunk he => hout ⟨chunk, he⟩
    simp only [State.commands] at kept
    refine ⟨fun c hc => hr c (kept ▸ hc), fun f hfin => ?_⟩
    by_cases same : (step s ev).1.finished = s.finished
    · exact hf f (same ▸ hfin)
    · rcases step_finished_changed s ev (by simpa [State.commands] using same) with hev | ⟨hnone, -⟩
      · exact absurd hev hout
      · simp only [State.commands] at hnone
        rw [hnone] at hfin
        cases hfin

end Linger.Session
