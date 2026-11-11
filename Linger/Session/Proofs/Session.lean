module

import all Linger.Session
import all Linger.Terminal.Vt
import all Linger.Terminal.Mediation
import all Linger.Session.Wire
import all Linger.Terminal.Render
-- The `Vt` seal makes the proof layer module-private, so the rungs this file
-- composes arrive through `import all`.
import all Linger.Terminal.Proofs.Mediation
import all Linger.Terminal.Proofs.Render
import all Linger.Session.Proofs.Wire
-- `Linger.Session.Proofs.Checkpoint` is here for one claim: `Checkpoint.load_live`, which makes
-- `LiveVt` provable for a *resumed* daemon (§Resume at the daemon, below).
import all Linger.Session.Proofs.Checkpoint
public import Linger.Session.Spec

/-! # §Detach / §Bound(session) — the daemon state machine theorems

**Friend module** (lean-modules Step 5): `import all Linger.Session` is
what lets these statements name `State`'s sealed bookkeeping fields —
`clients`, the `outSeq`/`lookSeq` pair, `scan`, `dirty` — which every plain
importer, the daemon included, can no longer read, poke or forge. No blanket
`public section`, for the Buf-friend reasons: statements naming private fields
cannot be public, `Linger/Session/Proofs/Driver.lean` and `Theorems/Contracts.lean` import
them with `import all`, and module-private is what keeps the `:= rfl`
proofs elaborating in the private scope.

THEOREMS.md rows:
* §Detach — sessions outlive clients. A session with zero clients still
  advances (output is never gated on attachment); a client detaching
  (or `detach-all`) cannot change the screen; attach touches only the
  dimensions, never the scrollback.
* §Bound — the session layer adds four bounded components on top of
  Vt's: the client list (≤ `maxClients`), the label table
  (≤ `maxLabels`), a wire decoder per client (≤ Wire's cap, never
  errored — a malformed peer is closed, not buffered) and the terminal
  scanner (`Bounded.scanOk`). `step` preserves all four against any
  event stream.
* §Frame, machine half — an `unknown` wire message is refused with an
  error reply and produces no state change.
-/

namespace Linger.Session

open Linger.Terminal
open Linger.Session.Wire (Msg)
open Linger.Terminal.Replay (Plan)

attribute [local grind] controlResize resizeOwned resize State.setClient

/-! ## §Frame (machine half) and other exact-shape facts -/

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
sees the daemon's own `fresh` and `unseen`. -/
theorem infoFields_seen (s : State) :
    ("fresh", toString s.seen.fresh) ∈ infoFields s ∧
      ("unseen", toString s.seen.unseen) ∈ infoFields s := by
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

/-! ## Label removal (pin-the-gaps item 3)

`.labelSet` was pinned four ways — the cap (`onMsg_labels_le`), the round trip
(`Linger/Session/Tests/Session.lean`), the forged-record channel (`infoText_records`) and the
boot cap. Its two *removal* siblings were pinned nowhere at all: no theorem, no
fixture, no pty assertion, covered only by the generic cap and by
`Wire.decode_encode_chunked`'s ∀-over-`Msg` codec claim. Both arms are unconditional, so
both take the exact-shape treatment `onMsg_screen` gets. -/

/-- **`linger unset <key>` removes exactly the named key.** The exact shape: the
key is the payload through `labelText` (invalid bytes → `""`, which matches no key
`.labelSet` can store since it rejects an empty key), the store is filtered, and
the only effect is `.done`. `rfl`, so a smuggled side effect — a vt touch, a
`.err`, an append — breaks it. -/
theorem onMsg_labelUnset (s : State) (c : Client) (k : List UInt8)
    (control : (c.attached && !c.sizer) = false) :
    onMsg s c (.labelUnset k) =
      ({ s with
          labels := s.labels.filter (fun kv => kv.1 != labelText k), dirty := true },
        [.send c.id .done]) := by
  simp [onMsg, control]

/-- …and the consequence, stated where a reader looks for it: after an unset, no
label carries that key. This is the promise; the shape above is how it is kept. -/
theorem onMsg_labelUnset_gone (s : State) (c : Client) (k : List UInt8)
    (control : (c.attached && !c.sizer) = false) :
    ∀ kv ∈ (onMsg s c (.labelUnset k)).1.labels, kv.1 ≠ labelText k := by
  intro kv hkv
  rw [onMsg_labelUnset s c k control] at hkv
  simp only [List.mem_filter, bne_iff_ne] at hkv
  exact hkv.2

/-- …and it removes *only* that key: every other label survives. Without this,
`onMsg_labelUnset_gone` is satisfied by an arm that clears the whole store — the
vacuity that makes a removal claim worthless. -/
theorem onMsg_labelUnset_keeps (s : State) (c : Client) (k : List UInt8) (kv : String × String)
    (control : (c.attached && !c.sizer) = false) (hmem : kv ∈ s.labels) (hne : kv.1 ≠ labelText k) :
    kv ∈ (onMsg s c (.labelUnset k)).1.labels := by
  rw [onMsg_labelUnset s c k control]
  simp only [List.mem_filter, bne_iff_ne]
  exact ⟨hmem, hne⟩

/-- **`linger clear` empties the store and marks it for checkpointing.** -/
theorem onMsg_labelClear (s : State) (c : Client) (control : (c.attached && !c.sizer) = false) :
    onMsg s c .labelClear =
      ({ s with
          labels := [], dirty := true },
        [.send c.id .done]) := by
  simp [onMsg, control]

/-- …the consequence, so the name a reader greps for states the fact. -/
theorem onMsg_labelClear_empty (s : State) (c : Client)
    (control : (c.attached && !c.sizer) = false) : (onMsg s c .labelClear).1.labels = [] := by
  rw [onMsg_labelClear s c control]

/-! ## §Detach -/

/-- Last-attacher detection uses the old roster; dirty state is saved exactly
once even when the bytes handler removes a malformed peer immediately, after any focus report
the leaver owes the program. -/
theorem closeClient_last_dirty (s : State) (id : Nat) (hd : s.dirty = true)
    (ha : s.clients.any (fun c => c.id == id && c.attached) = true)
    (hl : (s.dropClient id).clients.all (fun c => !c.attached) = true) :
    closeClient s id =
      ({ s.dropClient id with dirty := false },
        focusEffects ((s.client? id).any (·.sizer)) s.focused (s.dropClient id) ++
          [.checkpoint]) := by
  simp [closeClient, hd, ha, hl]

/-- Every effect of a disconnect is a checkpoint or the focus report that tells the program
nobody can type into it any more. -/
theorem closeClient_effects (s : State) (id : Nat) :
    ∀ e ∈ (closeClient s id).2, e = .checkpoint ∨ e = .writePty (focusReport false) :=
  closed_effects s id

/-- A watcher's disconnect owes the program no focus report: it could not type. -/
theorem closeClient_watcher (s : State) (id : Nat) {c : Client} (hc : s.client? id = some c)
    (hs : c.sizer = false) : ∀ e ∈ (closeClient s id).2, e = .checkpoint := by
  unfold closeClient focusEffects
  simp only [hc, Option.any_some, hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    List.nil_append]
  split <;> simp

@[simp]
theorem closeClient_vt (s : State) (id : Nat) : (closeClient s id).1.vt = s.vt := by
  unfold closeClient
  dsimp only
  split <;> rfl

/-- Closing a connection leaves the labels alone. -/
@[simp]
theorem closeClient_labels (s : State) (id : Nat) : (closeClient s id).1.labels = s.labels := by
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
          focusEffects ((s.client? id).any (·.sizer)) s.focused (s.dropClient id) ∨
        (step s (.closed id)).2 =
          focusEffects ((s.client? id).any (·.sizer)) s.focused (s.dropClient id) ++
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
          vt := r.vt, scan := r.scan, dirty := true, outSeq := s.outSeq + 1 },
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
`step` before exited notifications and close effects. -/
theorem step_childExited_scan (s : State) (outcome : Outcome) :
    (step s (.childExited outcome)).1.scan = .ground := by simp [step, Terminal.Mediation.finish]

/-- The incomplete prefix is the first effect segment, before the ending and its status go to
every attached or waiting client, then the closes, the checkpoint of the last screen, and daemon
exit. -/
theorem step_childExited_effects (s : State) (outcome : Outcome) :
    (step s (.childExited outcome)).2 =
      let flushed := Terminal.Mediation.finish s.scan
      let s' :=
        { s with
          exited := some outcome, scan := flushed.2 }
      let flush := broadcast s' flushed.1
      let notify :=
        s'.clients.filter (fun c => c.attached || c.waiting) |>.flatMap
          (fun c => [Effect.send c.id (.ended outcome), Effect.send c.id (.exited outcome.status)])
      let closes := s'.clients.map (fun c => Effect.close c.id)
      flush ++ notify ++ closes ++ [.checkpoint, .exit] := rfl

/-- A presentation broadcast deletes no checkpoint: it is only messages to clients. -/
theorem broadcast_no_dropCheckpoint (s : State) (bytes : List UInt8) :
    Effect.dropCheckpoint ∉ broadcast s bytes := by
  unfold broadcast outputMsgs
  split <;> simp

/-- **An ended session is a result**: when the program ends, the daemon saves the session's
last screen, as the program left it, just before it exits, and deletes nothing. So the session
stays listed with how its program ended, and `capture` shows what it left, until `kill`
discards it; `kill` itself deletes the checkpoint (`onMsg_kill`). -/
theorem step_childExited_keeps (s : State) (o : Outcome) :
    (∃ front,
        (step s (.childExited o)).2 = front ++ [.checkpoint, .exit] ∧
          Effect.dropCheckpoint ∉ front) ∧
      (step s (.childExited o)).1.terminal = s.terminal := by
  refine ⟨⟨_, by rw [step_childExited_effects], ?_⟩, rfl⟩
  simp [List.mem_append, broadcast_no_dropCheckpoint]

/-- `kill` from a client that may send it hangs up the program, deletes the checkpoint and ends
the daemon; a watcher's is refused and changes nothing. -/
theorem onMsg_kill (s : State) (c : Client) :
    onMsg s c .kill =
      if c.attached && !c.sizer then (s, [.send c.id (.err "read-only".toUTF8.toList)])
      else (s, [.killChild, .dropCheckpoint, .exit]) := rfl

/-- What a function makes of one member is a block of what it makes of the whole list. -/
theorem infix_flatMap_of_mem {α β : Type} {f : α → List β} {l : List α} {a : α} (h : a ∈ l) :
    f a <:+: l.flatMap f := by
  obtain ⟨front, back, rfl⟩ := List.append_of_mem h
  rw [List.flatMap_append, List.flatMap_cons, ← List.append_assoc]
  exact List.infix_append _ _ _

/-- **An ending reaches everyone listening**: when the program ends, every client attached to
the session or waiting for its end is told how the program ended and then the status a shell
would report for that ending, and the daemon's last effect is its exit. -/
theorem step_ended_reports (s : State) (o : Outcome) {c : Client} (hc : c ∈ s.roster)
    (listening : c.attached = true ∨ c.waiting = true) :
    [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
        (step s (.childExited o)).2 ∧
      (step s (.childExited o)).2.getLast? = some .exit := by
  rw [step_childExited_effects]
  dsimp only
  refine ⟨?_, by simp⟩
  have heard : c ∈ s.clients.filter (fun c => c.attached || c.waiting) :=
    List.mem_filter.mpr ⟨hc, by rcases listening with h | h <;> simp [h]⟩
  exact
    (infix_flatMap_of_mem (f := fun c =>
          [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)]) heard).trans
      ((List.infix_append _ _ _).trans (List.prefix_append _ _).isInfix)

/-- **`detach-all`'s whole purpose, as an equation** (pin-the-gaps item 2). The
verb changes no state at all, so everything it promises lives in the effect
list: one `.close` per *attached* client — the filter is the claim, since a
control connection (`linger send`, `linger info`) must survive a detach-all it
did not ask for — and a `.done` to the requester last, after the closes, so the
caller's own socket is not shut before its reply is queued. `rfl`, so dropping
the filter, reordering the `.done`, or closing the roster instead of the
attached subset each break it. -/
theorem onMsg_detachAll (s : State) (c : Client) (control : (c.attached && !c.sizer) = false) :
    onMsg s c .detachAll =
      (s,
        (s.clients.filter (·.attached) |>.map (fun c' => Effect.close c'.id)) ++
          [.send c.id .done]) := by
  simp [onMsg, control]

/-- Attach only resizes: the scrollback — the session's history — is
untouched by any attach/detach cycle (observer or not). -/
theorem onMsg_attach_sb (s : State) (c : Client) (cols rows : UInt32) :
    (onMsg s c (.attach cols rows)).1.vt.sb = s.vt.sb := by
  unfold onMsg
  grind [Vt.Vt.resize]

/-- **A same-size reattach leaves the emulator untouched.** `Vt.resize` resets the
scroll region and tab ruler (`top`/`bot`/`tabs`) unconditionally, so resizing at an
unchanged size wiped a child's `DECSTBM` and custom tab stops from the model — and
the kernel sends no `SIGWINCH` at an unchanged winsize, so the child never re-emits
them. The attach handler now resizes only on a genuine change, and this is why it is
safe: the whole `vt`, region and ruler included, is preserved (restore-conformance
Step 0 ledger 1). -/
theorem onMsg_attach_same_size_vt (s : State) (c : Client) (cols rows : UInt32)
    (hc : s.vt.cols = cols.toNat) (hr : s.vt.rows = rows.toNat) :
    (onMsg s c (.attach cols rows)).1.vt = s.vt := by
  unfold onMsg resizeOwned resize
  dsimp only
  split
  · rfl
  · split
    · simp [State.setClient, hc, hr]
    · simp [State.setClient]

/-- A connection gets one replay. Refusing a second attach keeps a decoded
message batch from building a backlog of immutable snapshots. -/
theorem onMsg_attach_already (s : State) (c : Client) (cols rows : UInt32) (h : c.attached = true) :
    onMsg s c (.attach cols rows) = (s, [.send c.id (.err "already attached".toUTF8.toList)]) := by
  simp [onMsg, h]

/-- Capture exactly the resulting attach snapshot, after any owned resize.
Later messages may change the runtime's state before it executes this plan. -/
theorem onMsg_attach_snapshot (s : State) (c : Client) (cols rows : UInt32)
    (h : c.attached = false) :
    ((onMsg s c (.attach cols rows)).2.filterMap
        (fun e =>
          match e with
          | .replay id plan => some (id, plan)
          | _ => none)) =
      [(c.id, Replay.start (onMsg s c (.attach cols rows)).1.vt)] := by
  unfold onMsg
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  unfold resizeOwned resize focusEffects
  dsimp only
  repeat' split
  all_goals simp

/-- Keystrokes from a full client go to the pty, not the emulator:
echo is the shell's job, so the machine's screen cannot drift. -/
theorem onMsg_input (s : State) (c : Client) (bs : List UInt8)
    (h : ¬(c.attached && !c.sizer) = true) : onMsg s c (.input bs) = (s, [.writePty bs]) := by
  unfold onMsg
  simp [h]

/-- A read-only observer's keyboard goes nowhere:
neither state nor pty sees it. -/
theorem onMsg_input_readonly (s : State) (c : Client) (bs : List UInt8)
    (h : (c.attached && !c.sizer) = true) : onMsg s c (.input bs) = (s, []) := by
  unfold onMsg
  simp [h]

/-! ## §Bound(session) -/

/-- The composite session bound. `Linger.Session.Bounds` (`Linger/Session/Spec.lean`) states
it through the state's observations; `bounded_iff_bounds` relates the two. -/
structure Bounded (s : State) : Prop where
  clientsLe : s.clients.length ≤ maxClients
  labelsLe : s.labels.length ≤ maxLabels
  decOk : ∀ c ∈ s.clients, c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload
  scanOk : s.scan.Bounded

/-- The private bound and the specification's agree. -/
theorem bounded_iff_bounds (s : State) :
    Bounded s ↔ Bounds State.roster State.labelList State.scanner s :=
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
of attach ordering: `attachSeq` hands out the sizer role by arrival, so a prepend would
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
      (s.ticked now).labels = s.labels ∧
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
    refine ⟨Nat.le_trans (dropClient_length_le s id) h.clientsLe, h.labelsLe, ?_, h.scanOk⟩
    intro c hmem
    exact h.decOk c (List.mem_filter.mp hmem).1

/-- `onMsg` never grows the client list. -/
theorem onMsg_clients_length_le (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).1.clients.length ≤ s.clients.length := by
  unfold onMsg
  grind

/-- `onMsg` keeps labels within the cap. -/
theorem onMsg_labels_le (s : State) (c : Client) (m : Msg) (h : s.labels.length ≤ maxLabels) :
    (onMsg s c m).1.labels.length ≤ maxLabels := by
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
  ⟨Nat.le_trans (onMsg_clients_length_le s c m) h.clientsLe, onMsg_labels_le s c m h.labelsLe,
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

/-- §Bound at the daemon level: no event stream can grow the client
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
  · -- tick
    split
    · exact ⟨hcl, hlb, hdec, hscan⟩
    · exact ⟨hcl, hlb, hdec, hscan⟩
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
  · split
    · exact h
    · exact h
  · exact h

open Linger.Terminal.Vt (Good) in
/-- §Total end-to-end: the screen state a daemon holds stays Good
whatever events arrive — adversarial clients and pty output included. -/
theorem step_vt_good (s : State) (ev : Event) (h : Good s.vt) : Good (step s ev).1.vt :=
  step_vt_preserves (fun _ cols rows hv => Linger.Terminal.Vt.Good.resize cols rows hv)
    (fun _ bytes hv => Linger.Terminal.Vt.Good.feed bytes hv) s ev h

/-! ## §Unread — the output counter

`unseen` is "output arrived while nobody was watching", and it is a property
of the **session**: `lookSeq` catches up on attach, on every output that
happens while somebody is attached, and on a capture (`.screen` — a capture is
a look, agent-cli Decision 1), so a one-off connection from a stranger creates
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

/-- **A capture is a look** (agent-cli Decision 1). The exact shape: the reply
is `Render.screenText` — the grid, never the ring — chunked and closed with
`.done`, and the ONLY state changes are the read mark catching up and the read's
answer being recorded. An exact equation, so any smuggled side effect (a vt
touch, a label change) breaks it. -/
theorem onMsg_screen (s : State) (c : Client) (ha : c.answered = false) :
    onMsg s c .screen =
      ({ s.setClient { c with answered := true } with lookSeq := s.outSeq },
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

/-- **§Unread over the daemon's whole life**: no event trace of any length —
adversarial clients, captures, attaches, hostile pty bytes, any interleaving —
makes the read mark overtake the output counter. `behind = outSeq - lookSeq`
is therefore a real count forever (a fresh daemon starts at `0 ≤ 0`), and the
agent loop "capture, then poll `behind`/`outseq`" rests on this rather than on
Nat subtraction clamping a lie to zero. -/
theorem run_lookSeq_le (s : State) (evs : List Event) (h : s.lookSeq ≤ s.outSeq) :
    (run s evs).1.lookSeq ≤ (run s evs).1.outSeq :=
  run_preserves s evs (P := fun s => s.lookSeq ≤ s.outSeq)
    (fun s ev _ hs => step_lookSeq_le s ev hs) h

/-! ## §Isolate — one client cannot reach another client's state

The concurrency question, at the layer where it is answerable. The
daemon is single-threaded: `poll` reports several ready fds, the
runtime reads each into its own `.bytes` event, and `step` serializes
them — so there are no data races by construction. What remains is
*interleaving*, and the hazard is cross-talk: could bytes from client A
corrupt client B's frame boundaries, or rewrite B's record?

§Isolate says no: `.bytes id` touches only client `id`'s record. Every
other client's decoder — mid-frame or not — is bit-identical
afterwards, whatever bytes arrive and however they were chunked (§Chunk
supplies the per-connection half: any split of A's stream yields the
same messages in the same order).
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

/-- §Isolate: bytes from one client cannot alter another client's
record — including its wire decoder, so a peer stuck mid-frame stays
mid-frame and resumes correctly on its next chunk. Daemon-level
concurrency safety is this, plus §Chunk (per-connection ordering),
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
def WF (s : State) : Prop := Bounded s ∧ Linger.Terminal.Vt.Good s.vt

theorem step_wf (s : State) (ev : Event) (h : WF s) : WF (step s ev).1 :=
  ⟨step_bounded s ev h.1, step_vt_good s ev h.2⟩

/-- §Bound + §Total over the daemon's whole life: no event trace of any
length — adversarial clients, hostile pty bytes, any interleaving — can
break the bounds or the screen invariant. -/
theorem run_wf (s : State) (evs : List Event) (h : WF s) : WF (run s evs).1 :=
  run_preserves s evs (fun s ev _ hs => step_wf s ev hs) h

/-- §Isolate over a whole trace: one client's entire byte stream,
however chunked, leaves every other client's record — decoder included
— bit-identical. -/
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other := by
  apply run_preserves _ _ (P := fun t => t.client? other = s.client? other) ?_ rfl
  intro t ev hev ht
  obtain ⟨chunk, _, rfl⟩ := List.mem_map.mp hev
  rw [step_bytes_isolates t id chunk h]
  exact ht

/-! ## §Renderable lifted to the daemon's whole life

The emulator-level invariant is only useful if the *daemon's* terminal satisfies
it, for any event trace. A session does exactly three things to its `Vt`: feeds
it pty bytes (through the mediator, whose VT projection is `Vt.feed` —
`Mediation.feed_vt`), resizes it on attach or resize, and nothing else. Those are
precisely `LiveReachableVt`'s constructors, so the lift is an induction with no
new content — which is the point: the replay theorem may assume a *reachable*
grid without that assumption smuggling in a side condition.
-/

open Linger.Terminal.Vt (Live LiveReachableVt Renderable)

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
    Renderable (run s evs).1.vt :=
  Linger.Terminal.Vt.renderable_of_liveReachable (run_vt_live s evs h)

/-- A fresh boot through `State.boot`, the one door the runtime walks through,
satisfies the hypothesis, so the statement above is not conditional in practice. -/
theorem liveVt_boot (cols rows : Nat) (ls mk : List (String × String)) :
    LiveVt (State.boot (Vt.Vt.init cols rows) ls mk) := Live.init cols rows

/-! ## §Resume at the daemon — the other door into `State.boot`

`liveVt_boot` covers a *fresh* boot. `Linger/Session/Shell/Daemon.lean` has a second
source for the `vt0` it boots with:

```
let vt0 := Linger.Session.bootVt (restore.map (·.1))
```

where `restore` is `Runtime.Resume.loadCkpt`'s result — `ck.vt` for a
`Checkpoint.loadBytes bytes = some ck`, which `Checkpoint.loadBytes_eq` turns into
`Checkpoint.load bytes.data.toList = some ck`. Until the `ofDecoded` rung there was no way to
say `LiveVt` of that half, so a resumed session's `Renderable` had to be assembled
by the reader out of `renderable_feed`/`renderable_resize` one operation at a time.
The claims below close that, and the shape to mirror is `boot_wf`/`run_boot_wf`
in the next section: a door lemma per source, one hypothesised whole-life claim, and
then the hypothesis-free form over the term the daemon actually computes. -/

/-- **The resume door.** A daemon booting from any byte string that loads at all holds a
state a live session can hold. `Checkpoint.load_live` is the whole content; what this adds
is that `State.boot` does not disturb it — the `take maxLabels` `boot` performs touches the
labels, never the `Vt`. -/
theorem liveVt_boot_of_load {l : List UInt8} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.load l = some c) (ls mk : List (String × String)) :
    LiveVt (State.boot c.vt ls mk) := Checkpoint.load_live h

/-- **`Daemon.lean`'s `vt0`, as a pure function of the bytes on disk.** The runtime writes

```
let vt0 := Linger.Session.bootVt (restore.map (·.1))
```

with `restore` from `Runtime.Resume.loadCkpt`, whose `some` case is `(ck.vt, …)` for a
`Checkpoint.loadBytes bytes = some ck`; it is `none` for a missing file or for bytes that do
not decode (torn write, foreign tag, corrupt payload), and an existing file that cannot be
read throws before the boot. So this is that expression with the `IO` peeled off, and `b`
ranges over every byte string that could be on disk.

**Named rather than inlined**, for the reason `Vt.decodedOk` and `stripMagic` are named:
the two claims below repeat it six times between them and would be unreadable spelled out.
The daemon calls `bootVt` itself, so the model and the runtime share the fallback by
construction: `scripts/gates.sh` ties the daemon's call, and `Theorems/Contracts.lean` ties
this definition to `bootVt` over `Checkpoint.loadBytes`. -/
def resumeVt (b : ByteArray) : Vt.Vt := bootVt ((Checkpoint.loadBytes b).map (·.vt))

/-- **Both doors, in one step.** `bootVt`'s two branches are exactly the daemon's two
sources for `vt0`: `none` is a fresh `Vt.init 80 24`, `some` is a decoded checkpoint. This
is where the `ofDecoded` rung is load-bearing — the `some` branch has no other witness.
Stated over `bootVt` itself, the term `Daemon.lean` calls. -/
theorem liveReachableVt_resumeVt (b : ByteArray) :
    Linger.Terminal.Vt.LiveReachableVt (bootVt ((Checkpoint.loadBytes b).map (·.vt))) := by
  unfold bootVt
  rcases hl : Checkpoint.loadBytes b with - | c
  · exact Live.init 80 24
  · exact Checkpoint.loadBytes_live hl

/-- **§Renderable over the daemon's whole life, from either door.** The `LiveVt` analogue
of `run_boot_wf`: whatever a session has been through — adversarial clients, hostile pty
bytes, resizes, any interleaving — its terminal is still one a live session can hold,
whether it booted fresh (`liveVt_boot`) or resumed (`liveVt_boot_of_load`). -/
theorem run_boot_vt_live (vt : Vt.Vt) (labels metaKv : List (String × String)) (evs : List Event)
    (h : Linger.Terminal.Vt.LiveReachableVt vt) :
    LiveVt (run (State.boot vt labels metaKv) evs).1 := run_vt_live _ _ h

/-- **The A2 anchor for the screen, made structural.** Every state the daemon can *possess*
— every state reachable from any boot, which by the `State` seal is all of them — has a
grid `Render.restore` can express and a tab ruler the width of it.

Stated as one theorem rather than a chain because the chain is what a reader was previously
left to assemble, and the resumed half of it did not exist: `run_vt_renderable` needed
`LiveVt s`, and nothing supplied that for a decoded `vt0`. `TabsOk` rides along because it
is the second hypothesis `Render.restore_tabs_any` and `Resume.resume_tabs` ask for and
`Renderable` does not carry. -/
theorem run_boot_vt_shape (vt : Vt.Vt) (labels metaKv : List (String × String)) (evs : List Event)
    (h : Linger.Terminal.Vt.LiveReachableVt vt) :
    Renderable (run (State.boot vt labels metaKv) evs).1.vt ∧
      Linger.Terminal.Vt.TabsOk (run (State.boot vt labels metaKv) evs).1.vt :=
  ⟨Linger.Terminal.Vt.renderable_of_liveReachable (run_boot_vt_live vt labels metaKv evs h),
    Linger.Terminal.Vt.tabsOk_of_liveReachable (run_boot_vt_live vt labels metaKv evs h)⟩

/-- **The same claim with no hypothesis at all, over the term the daemon computes.** `b` is
an arbitrary `ByteArray` — a corrupt file, a truncated one, a hostile one, or a real
checkpoint — and `resumeVt b` is `Daemon.lean`'s `vt0`. Both doors are the two branches of
`bootVt`, so this is the whole of "every screen the daemon can possess is one the emitter
can repaint, and every ruler is the width of its screen", quantified over every byte string
that could be on disk and every event trace.

Unprovable before the `ofDecoded` rung: the `some` branch had no `LiveVt`. -/
theorem run_resume_vt_shape (b : ByteArray) (labels metaKv : List (String × String))
    (evs : List Event) :
    Renderable (run (State.boot (resumeVt b) labels metaKv) evs).1.vt ∧
      Linger.Terminal.Vt.TabsOk (run (State.boot (resumeVt b) labels metaKv) evs).1.vt :=
  run_boot_vt_shape _ labels metaKv evs (liveReachableVt_resumeVt b)

/-- **A1 across a *second* reboot.** The checkpoint a resumed session writes loads back
exactly, for any bytes it was resumed from and any trace it then ran. `load_save_live`'s
three hypotheses are discharged in one step by the same reachability, which is the point:
reboot-resume is idempotent rather than one-shot, and before the rung this could only be
said of a session that had never been resumed.

The `.quiesce` on the right is content, not decoration — the round trip is exact *modulo*
the parser state a checkpoint deliberately forgets (`Checkpoint.wVt`). A poll boundary
can split an escape or UTF-8 sequence, so it does not establish parser quiescence. -/
theorem run_resume_load_save (b : ByteArray) (labels metaKv : List (String × String))
    (evs : List Event) (cwd : String) :
    Checkpoint.loadBytes
        (Checkpoint.saveBytes
          { vt := (run (State.boot (resumeVt b) labels metaKv) evs).1.vt, cwd,
            labels := (run (State.boot (resumeVt b) labels metaKv) evs).1.labels }) =
      some
        { vt := (run (State.boot (resumeVt b) labels metaKv) evs).1.vt.quiesce, cwd,
          labels := (run (State.boot (resumeVt b) labels metaKv) evs).1.labels } :=
  Checkpoint.loadBytes_saveBytes_live _
    (run_boot_vt_live _ labels metaKv evs (liveReachableVt_resumeVt b))

/-! ## §Bound at the door — boot is well-formed, so every daemon state is

With the constructor private (lean-modules Step 5), `State.boot` is the only
way a `State` comes to exist outside this module's friends, and `step` the
only way forward — so `boot_wf ∘ run_wf` stops being "the invariant holds if
the runtime starts politely" and covers every state the daemon can possess.
The labels conjunct is what `boot`'s `take` buys: before it, a corrupt
checkpoint's label list booted straight past `maxLabels` and `Bounded` was
simply false of a resumed daemon (the gap that sized this step). The `Good vt`
hypothesis is honest: a fresh boot has `Good (Vt.init …)`, and the resume
path's decoded emulator carries it from the checkpoint theorems' side. -/

theorem boot_wf (vt : Vt.Vt) (labels metaKv : List (String × String))
    (h : Linger.Terminal.Vt.Good vt) : WF (State.boot vt labels metaKv) :=
  ⟨⟨Nat.zero_le _, List.length_take_le _ _, nofun, trivial⟩, h⟩

/-- **The A2 anchor made structural**: every state reachable from any boot —
which, by the seal, is every state the daemon can possess — is well-formed,
whatever the trace: adversarial clients, hostile pty bytes, forged
checkpoints' label lists, any interleaving. -/
theorem run_boot_wf (vt : Vt.Vt) (labels metaKv : List (String × String)) (evs : List Event)
    (h : Linger.Terminal.Vt.Good vt) :
    WF (run (State.boot vt labels metaKv) evs).1 := run_wf _ _ (boot_wf vt labels metaKv h)

/-- **Only the size owner resizes the pty** — as a theorem rather than a
convention. `resizeOwned` emits a `resizePty` only for the client the size-ownership
cascade (`sizeOwner`: newest attached real-terminal attacher) actually selected — a
read-only observer or an older mirror never moves the pty out from under the active
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
    (h : (onMsg s c m).1.labels ≠ s.labels) : (onMsg s c m).1.dirty = true := by
  unfold onMsg at *
  grind

/-! ## §Size — a control resize never overrides an attached sizer

`linger resize` (agent-cli Decision 3) lets an agent size a *detached* session
so wrap is deterministic before a capture. The size-owner rule extends rather than
bends: an attached sizer always wins, and the refusal is loud — an agent must
not believe a size it never got. -/

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
    (ha : c.attached = true) (hs : c.sizer = true) : (s.setClient c).focused = true := by
  have h1 := client?_setClient (c := c) h
  unfold State.client? at h1
  simp only [State.focused, List.any_eq_true]
  exact ⟨c, List.mem_of_find?_eq_some h1, by simp [ha, hs]⟩

/-- **Focus follows typing**: when a client with a terminal of its own attaches to a session
nobody could type into, a program that enabled focus reporting hears that it gained focus. -/
theorem onMsg_attach_focus (s : State) (c : Client) (cols rows : UInt32)
    (hc : s.client? c.id = some c) (h : c.attached = false)
    (hsize : (cols != 0 && rows != 0) = true) (hunfocused : s.focused = false)
    (hmode : s.vt.getModes.focusEvents = true) :
    Effect.writePty (focusReport true) ∈ (onMsg s c (.attach cols rows)).2 := by
  let c' : Client :=
    { c with
      attached := true, sizer := cols != 0 && rows != 0, seq := s.attachSeq, cols, rows }
  let s1 : State :=
    { s.setClient c' with
      attachSeq := s.attachSeq + 1, lookSeq := s.outSeq }
  have hfocused : (resizeOwned s1 c').1.focused = true := by
    have hf : s1.focused = true := focused_setClient (c := c') hc rfl hsize
    simp only [State.focused, (resizeOwned_frame s1 c').1]
    exact hf
  have hmodes : (resizeOwned s1 c').1.vt.getModes = s.vt.getModes := (resizeOwned_frame s1 c').2
  have key :
    focusEffects (cols != 0 && rows != 0) s.focused (resizeOwned s1 c').1 =
      [.writePty (focusReport true)] := by
    simp only [focusEffects, hsize, hunfocused, hfocused, hmodes, hmode]
    rfl
  unfold onMsg
  dsimp only
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  show
    Effect.writePty (focusReport true) ∈
      (resizeOwned s1 c').2 ++
        focusEffects (cols != 0 && rows != 0) s.focused (resizeOwned s1 c').1 ++
        _ ++
        _
  rw [key]
  simp

/-- …and when the last client that could type leaves, the program hears that it lost focus. -/
theorem closeClient_focus (s : State) (id : Nat) {c : Client} (hc : s.client? id = some c)
    (hs : c.sizer = true) (hfocused : s.focused = true) (hlast : (s.dropClient id).focused = false)
    (hmode : s.vt.getModes.focusEvents = true) :
    Effect.writePty (focusReport false) ∈ (closeClient s id).2 := by
  have key :
    focusEffects ((s.client? id).any (·.sizer)) s.focused (s.dropClient id) =
      [.writePty (focusReport false)] := by
    have hm : (s.dropClient id).vt.getModes.focusEvents = true := hmode
    simp only [focusEffects, hc, Option.any_some, hs, hfocused, hlast, hm]
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
        (c'.attached = false → c.attached = false ∧ ∀ cols rows, m ≠ .attach cols rows) := by
  cases m with
  | attach cols rows =>
    unfold onMsg
    dsimp only
    split
    · rename_i ha
      exact ⟨c, hc, by simp [costly], by simp [ha]⟩
    · let c' : Client :=
        { c with
          attached := true, sizer := cols != 0 && rows != 0, seq := s.attachSeq, cols, rows }
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

/-- …and, from a connection that is neither attached nor attaching, no pty resize. -/
theorem onMsg_unresized (s : State) (c : Client) (m : Msg)
    (h : c.answered = true ∨ costly c m = false) (ha : c.attached = false)
    (hm : ∀ cols rows, m ≠ .attach cols rows) : (onMsg s c m).2.all (!·.resizes) := by
  cases m
  case attach cols rows => exact absurd rfl (hm cols rows)
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
sizer's resizes follow its terminal and are outside this bound, and an attach replays
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

/-! ## §Row / §Status integrity — a listing record cannot be forged

`Status.name_clean` proves the *status* column carries neither framing byte, which is
what lets the porcelain be tab-separated with no escaping pass. This is the same
promise for every **other** column — and it was false until 2026-08-17.

`infoText` framed its records with a `String` interpolation, so a label value
containing a newline forged an extra record: `.labelSet` applies no filter and
`linger set` passes the value through, so `linger set s x=$'a\nstatus\tlive'` put a
`status`/`state` pair into the listing that `Status.classify`'s consumers would read as
the session's state. Recorded as Step 0 ledger item 2 in
`specs/archive/restore-conformance.md`; fixed at the **emit site**, which is why the claims
below need no hypothesis about where a field came from.

The fix is also what makes them provable at all: the old shape ended in
`String.toUTF8`, and a `String` does not reduce in the kernel — the same argument
`Linger/Terminal/Render.lean`'s header makes, and the same reason `Render.history` was the
last byte stream to acquire a proof rather than merely a *bound*: it too was assembled
through `String` until `rowText` was rebuilt on `List UInt8`, which is what earned it
`history_framing`/`history_lines`. `Theorems/Coverage.lean` now requires exact
constant occurrences in theorem types; `Verify/Coverage.lean` classifies emitted streams.
`infoText` now builds
`List UInt8` directly for the same reason. -/

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

/-! ## §Chunk at the session layer — what a client receives is what was sent

A3 says the *transport* is invisible: any re-chunking of an encoded stream decodes to
exactly that stream. The session does its own framing on top of that — `outputMsgs`
splits a payload into ≤ 64 KiB `output` frames — and that framing had no claim at all.
`chunksOf`, the function that does it, appeared in `Theorems/` exactly once, in a
comment; it is the same blindness in the old coverage gate that let `infoText` pass.

Two claims, and they are the two properties the runtime depends on: the split loses
nothing (so a reattaching client's repaint is complete) and no frame exceeds the cap
(so `Wire`'s §Bound well-formedness holds of what the daemon actually sends). -/

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
daemon sends well-formed by `Wire`'s §Bound measure. -/
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
its first `maxLabels` restored labels and an idle scanner. -/
theorem boot_observed (vt : Vt.Vt) (labels metaKv : List (String × String)) :
    bootVt none = Vt.Vt.init 80 24 ∧
      bootVt (some vt) = vt ∧
      (State.boot vt labels metaKv).terminal = vt ∧
      (State.boot vt labels metaKv).roster = [] ∧
      (State.boot vt labels metaKv).labelList = labels.take maxLabels ∧
      (State.boot vt labels metaKv).scanner = .ground := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

An attached client that did not give a size is a watcher. Whatever bytes it sends, however
chunked, leave the terminal and the labels alone, and every effect they cause is a message to
it, its own disconnection or a checkpoint: it can look and leave, and nothing else. Its records
stay watchers' across the trace: no message detaches it or makes it a sizer, and a decoder error
removes every record with its identifier. -/

/-- An effect a watcher's bytes may cause: a message to it, its own disconnection, or a
checkpoint. -/
def watcherEffect (id : Nat) : Effect Plan → Bool
  | .send to _ | .close to => to == id
  | .checkpoint => true
  | _ => false

/-- Every record the identifier finds is attached and gave no size. -/
def Watches (s : State) (id : Nat) : Prop :=
  ∀ c, s.client? id = some c → c.attached = true ∧ c.sizer = false

/-- The record an identifier finds decides `Watches` for it. -/
theorem watches_of_client? {s : State} {c : Client} (hc : s.client? c.id = some c)
    (ha : c.attached = true) (hs : c.sizer = false) : Watches s c.id := by
  intro c' h
  rw [hc] at h
  cases h
  exact ⟨ha, hs⟩

/-- Rewriting a found record with a watcher's makes the identifier a watcher's. -/
theorem watches_setClient {s : State} {c c0 : Client} {id : Nat} (hid : c.id = id)
    (hc : s.client? id = some c0) (ha : c.attached = true) (hs : c.sizer = false) :
    Watches (s.setClient c) id := by
  subst hid
  exact watches_of_client? (client?_setClient hc) ha hs

/-- A message from an attached sender keeps its record attached and its sizer flag as it was. -/
theorem onMsg_watcher_record (s : State) (c : Client) (m : Msg) (hc : s.client? c.id = some c)
    (ha : c.attached = true) :
    ∃ c',
      (onMsg s c m).1.client? c.id = some c' ∧ c'.attached = c.attached ∧ c'.sizer = c.sizer := by
  cases m with
  | attach cols rows =>
    exact
      ⟨c, by
        rw [onMsg_attach_already s c cols rows ha]; exact hc, rfl, rfl⟩
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
    (hs : c.sizer = false) : (onMsg s c m).2.all (watcherEffect c.id) = true := by
  cases m
  all_goals
    unfold onMsg resizeOwned resize controlResize infoMsgs
    dsimp only
    repeat' split
  all_goals simp_all [watcherEffect, outputMsgs]

/-- A message from a watcher leaves the terminal alone. -/
theorem onMsg_watcher_vt (s : State) (c : Client) (m : Msg) (ha : c.attached = true)
    (hs : c.sizer = false) : (onMsg s c m).1.vt = s.vt := by
  cases m
  all_goals
    unfold onMsg resizeOwned resize
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- A message from a watcher leaves the labels alone. -/
theorem onMsg_watcher_labels (s : State) (c : Client) (m : Msg) (ha : c.attached = true)
    (hs : c.sizer = false) : (onMsg s c m).1.labels = s.labels := by
  cases m
  all_goals
    unfold onMsg resizeOwned resize
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- A message batch from a watcher keeps its records watchers', leaves the terminal and the
labels alone, and adds only effects a watcher may cause. -/
theorem feedMsgs_watcher (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (hw : Watches acc.1 id) (hq : acc.2.all (watcherEffect id) = true) :
    Watches (feedMsgs id msgs acc).1 id ∧
      (feedMsgs id msgs acc).1.vt = acc.1.vt ∧
      (feedMsgs id msgs acc).1.labels = acc.1.labels ∧
      (feedMsgs id msgs acc).2.all (watcherEffect id) = true := by
  apply
    feedMsgs_induct id msgs acc (P := fun r =>
      Watches r.1 id ∧
        r.1.vt = acc.1.vt ∧ r.1.labels = acc.1.labels ∧ r.2.all (watcherEffect id) = true)
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
      (step s (.bytes id chunk)).1.labels = s.labels ∧
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
      (run s (chunks.map (Event.bytes id))).1.labels = s.labels ∧
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
chunked, leave the terminal and the labels unchanged, and every effect they cause is a message to
the watcher, its own disconnection or a checkpoint. -/
theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (run s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (run s (chunks.map (Event.bytes id))).1.labelList = s.labelList ∧
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
    (s.setClient c).focused = s.clients.any (fun x => x.id != c.id && (x.attached && x.sizer)) := by
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
theorem onMsg_attach_writePty (t : State) (c : Client) (cols rows : UInt32) (bytes : List UInt8) :
    Effect.writePty bytes ∈ (onMsg t c (.attach cols rows)).2 ↔
      c.attached = false ∧
        Effect.writePty bytes ∈
          focusEffects (cols != 0 && rows != 0) t.focused
            (resizeOwned
                {
                  t.setClient
                    { c with
                      attached := true, sizer := cols != 0 && rows != 0, seq := t.attachSeq, cols,
                      rows } with
                  attachSeq := t.attachSeq + 1, lookSeq := t.outSeq }
                { c with
                  attached := true, sizer := cols != 0 && rows != 0, seq := t.attachSeq, cols,
                  rows }).1 := by
  let c' : Client :=
    { c with
      attached := true, sizer := cols != 0 && rows != 0, seq := t.attachSeq, cols, rows }
  let t1 : State :=
    { t.setClient c' with
      attachSeq := t.attachSeq + 1, lookSeq := t.outSeq }
  have hro := resizeOwned_effects t1 c'
  unfold onMsg
  dsimp only
  cases ha : c.attached
  · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    show
      Effect.writePty bytes ∈
          (resizeOwned t1 c').2 ++
            focusEffects (cols != 0 && rows != 0) t.focused (resizeOwned t1 c').1 ++
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
a connection not yet attached and has a terminal of its own, and nobody else could type. -/
theorem step_attach_focus (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {cols rows : UInt32} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.attach cols rows])) (healthy : dec.errored = false)
    (bytes : List UInt8) :
    Effect.writePty bytes ∈ (step s (.bytes id chunk)).2 ↔
      bytes = [0x1B, 0x5B, 0x49] ∧
        s.terminal.getModes.focusEvents = true ∧
        c.attached = false ∧
        cols ≠ 0 ∧
        rows ≠ 0 ∧ ∀ other ∈ s.roster, other.id ≠ id → (other.attached && other.sizer) = false := by
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
      attached := true, sizer := cols != 0 && rows != 0, seq := t.attachSeq, cols, rows }
  let t1 : State :=
    { t.setClient c' with
      attachSeq := t.attachSeq + 1, lookSeq := t.outSeq }
  show
    (c1.attached = false ∧
        Effect.writePty bytes ∈
          focusEffects (cols != 0 && rows != 0) t.focused (resizeOwned t1 c').1) ↔
      _
  have h1 : t.client? c'.id = some c1 := client?_setClient (c := c1) hc'
  have hmodes : (resizeOwned t1 c').1.vt.getModes = s.vt.getModes := (resizeOwned_frame t1 c').2
  have hafter (hs : (cols != 0 && rows != 0) = true) : (resizeOwned t1 c').1.focused = true := by
    have hf : (t.setClient c').focused = true := focused_setClient (c := c') h1 rfl hs
    simp only [State.focused, (resizeOwned_frame t1 c').1]
    exact hf
  cases ha : c.attached
  · have hbefore : t.focused = s.clients.any (fun x => x.id != id && (x.attached && x.sizer)) := by
      rw [focused_setClient_unattached s c1 ha]
      simp only [c1, hid]
    unfold focusEffects
    rw [hbefore]
    cases hs : (cols != 0 && rows != 0)
    · have hz : ¬(cols ≠ 0 ∧ rows ≠ 0) := by simpa using hs
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, and_false,
        false_iff]
      exact fun ⟨_, _, _, h, h', _⟩ => hz ⟨h, h'⟩
    · rw [hafter hs, hmodes]
      have hnz : cols ≠ 0 ∧ rows ≠ 0 := by simpa using hs
      simp only [Bool.true_and, focusReport, ↓reduceIte, State.terminal, State.roster]
      constructor
      · intro ⟨_, hm⟩
        split at hm
        · rename_i hcond
          simp only [List.mem_singleton, Effect.writePty.injEq] at hm
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true] at hcond
          refine ⟨hm, hcond.2, by simp, hnz.1, hnz.2, fun other hother hne => ?_⟩
          have := hcond.1
          simp only [List.any_eq_false] at this
          have := this other hother
          cases h : other.attached && other.sizer
          · rfl
          · simp_all
        · simp at hm
      · rintro ⟨rfl, hmode, -, -, -, hnobody⟩
        refine ⟨by simp, ?_⟩
        have hnone : s.clients.any (fun x => x.id != id && (x.attached && x.sizer)) = false := by
          simp only [List.any_eq_false]
          intro x hx
          by_cases hxid : x.id = id
          · simp [hxid]
          · have := hnobody x hx hxid
            simp_all
        simp [hnone]
        exact hmode
  · simp

/-- **…and on close**: closing a connection writes to the program only `CSI O`, and exactly when
the program enabled focus reporting and the connection, which had a terminal of its own, was the
last through which someone could type. -/
theorem step_closed_focus (s : State) (id : Nat) (bytes : List UInt8) :
    Effect.writePty bytes ∈ (step s (.closed id)).2 ↔
      bytes = [0x1B, 0x5B, 0x4F] ∧
        s.terminal.getModes.focusEvents = true ∧
        (s.client? id).any (·.sizer) = true ∧
        s.roster.any (fun c => c.attached && c.sizer) = true ∧
        (step s (.closed id)).1.roster.any (fun c => c.attached && c.sizer) = false := by
  have hroster : (step s (.closed id)).1.roster = s.clients.filter (·.id != id) :=
    closeClient_clients s id
  rw [hroster]
  have hsub :
    (s.clients.filter (·.id != id)).any (fun c => c.attached && c.sizer) = true →
      s.clients.any (fun c => c.attached && c.sizer) = true := by
    simp only [List.any_eq_true, List.mem_filter]
    rintro ⟨x, ⟨hx, -⟩, h⟩
    exact ⟨x, hx, h⟩
  have hfx :
    Effect.writePty bytes ∈ (step s (.closed id)).2 ↔
      Effect.writePty bytes ∈
        focusEffects ((s.client? id).any (·.sizer)) s.focused (s.dropClient id) := by
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
      (step s (.bytes id chunk)).1.labelList = s.labelList := by
  have hid : c.id = id := client?_id hc
  rw [step_bytes_single hc read healthy, onMsg_unknown]
  exact ⟨by simp [hid], rfl, rfl⟩

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
theorem onMsg_labels_kept (s : State) (c : Client) (m : Msg) (h : ¬m.ChangesLabels) :
    (onMsg s c m).1.labels = s.labels := by
  cases m
  all_goals simp only [Msg.ChangesLabels, not_true_eq_false] at h
  all_goals
    unfold onMsg controlResize resizeOwned resize focusEffects infoMsgs outputMsgs
    dsimp only
    repeat' split
  all_goals simp_all [State.setClient]

/-- A batch with no label request leaves the labels as they were. -/
theorem feedMsgs_labels (id : Nat) (msgs : List Msg) (acc : State × List (Effect Plan))
    (none : ∀ m ∈ msgs, ¬m.ChangesLabels) : (feedMsgs id msgs acc).1.labels = acc.1.labels := by
  exact
    feedMsgs_induct id msgs acc (P := fun r => r.1.labels = acc.1.labels)
      (fun current c m hm _ _ _ hs => (onMsg_labels_kept current.1 c m (none m hm)).trans hs) rfl

/-- **The labels have one source**: an event that changes them is a read, from a client that is
not a watcher, that holds a label request. -/
theorem step_labels_sources (s : State) (ev : Event)
    (changed : (step s ev).1.labelList ≠ s.labelList) :
    ∃ id chunk c,
      ev = .bytes id chunk ∧
        s.client? id = some c ∧
        (c.attached = false ∨ c.sizer = true) ∧
        ∃ m ∈ (c.decoder.feed chunk).2, m.ChangesLabels := by
  cases ev with
  | bytes id chunk =>
    cases hc : s.client? id with
    | none => exact absurd (by simp [step, hc, State.labelList]) changed
    | some c =>
      refine ⟨id, chunk, c, rfl, hc, ?_, ?_⟩
      · by_cases hw : c.attached = true ∧ c.sizer = false
        · have hwatch : Watches s id := by
            intro c' h'
            rw [hc] at h'
            cases h'
            exact hw
          exact absurd (step_bytes_watcher s id chunk hwatch).2.2.1 changed
        · cases ha : c.attached <;> cases hs : c.sizer <;> simp_all
      · apply Classical.byContradiction
        intro hnone
        apply changed
        simp only [not_exists, not_and] at hnone
        simp only [step, hc, State.labelList]
        split
        · simp
        · rw [feedMsgs_labels]
          · simp [State.setClient]
          · exact fun m hm => hnone m hm
  | connected id =>
    refine absurd ?_ changed
    dsimp only [step]
    split <;> rfl
  | closed id => exact absurd (by simp [step, State.labelList]) changed
  | ptyOut chunk => exact absurd rfl changed
  | childExited o => exact absurd rfl changed
  | tick now =>
    refine absurd ?_ changed
    dsimp only [step]
    split <;> rfl
  | checkpointFailed => exact absurd rfl changed

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
  | tick now =>
    right
    show Sized (step s (.tick now)).1.vt
    dsimp only [step]
    split <;> exact kept
  | checkpointFailed => exact .inr kept

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
    (hc : t.client? id = some c) (typist : c.attached = false ∨ c.sizer = true)
    (effs : List (Effect Plan)) (clean : Effect.close id ∉ effs ∧ Effect.exit ∉ effs) :
    feedMsgs id (inputs.map Msg.input) (t, effs) = (t, effs ++ inputs.map Effect.writePty) := by
  induction inputs generalizing effs with
  | nil => simp [feedMsgs]
  | cons bytes inputs
    ih =>
    have stays : onMsg t c (.input bytes) = (t, [.writePty bytes]) := by
      unfold onMsg
      rcases typist with h | h <;> simp [h]
    have next := ih (effs ++ [.writePty bytes]) (by simpa using clean)
    simp only [feedMsgs, List.map_cons, List.foldl_cons] at next ⊢
    simp only [List.contains_eq_mem, decide_eq_true_eq, clean.1, clean.2, Bool.or_self, ↓reduceIte,
      hc, stays] at ⊢
    simpa using next

/-- **A typist's input is written exactly**: a read of input messages from a client that may
type is one write per message, its bytes, in order, and nothing else. -/
theorem step_input_exact (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {inputs : List (List UInt8)} (hc : s.client? id = some c)
    (typist : c.attached = false ∨ c.sizer = true)
    (read : c.decoder.feed chunk = (dec, inputs.map Msg.input)) (healthy : dec.errored = false) :
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

end Linger.Session
