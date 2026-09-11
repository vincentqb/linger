module

public import Linger.Core.Session
public import Theorems.Wire
public import Theorems.Vt
public import Theorems.Terminal
public import Theorems.Render
import all Linger.Core.Session
import all Linger.Core.Vt
import all Linger.Core.Terminal
import all Linger.Core.Wire
import all Linger.Core.Render

/-! # §Detach / §Bound(session) — the daemon state machine theorems

**Friend module** (lean-modules Step 5): `import all Linger.Core.Session` is
what lets these statements name `State`'s sealed bookkeeping fields —
`clients`, the `outSeq`/`lookSeq` pair, `scan`, `dirty` — which every plain
importer, the daemon included, can no longer read, poke or forge. No blanket
`public section`, for the Buf-friend reasons: statements naming private fields
cannot be public, nothing imports these theorems as lemmas (the root builds
them, which is their job), and module-private is what keeps the `:= rfl`
proofs elaborating in the private scope.

THEOREMS.md rows:
* §Detach — the zmx decoupling. A session with zero clients still
  advances (output is never gated on attachment); a client detaching
  (or `detach-all`) cannot change the screen; attach touches only the
  dimensions, never the scrollback.
* §Bound — the session layer adds three stores on top of Vt's: the
  client list (≤ `maxClients`), the label table (≤ `maxLabels`), and a
  wire decoder per client (≤ Wire's cap, never errored — a malformed
  peer is closed, not buffered). `step` preserves all three against
  any event stream.
* §Frame, machine half — an `unknown` wire message produces no state
  change and no effects.
-/

namespace Linger.Core.Session

open Linger.Core.Wire (Msg)

/-! ## §Frame (machine half) and other exact-shape facts -/

theorem onMsg_unknown (s : State) (c : Client) (t : UInt8) (p : List UInt8) :
    onMsg s c (.unknown t p) = (s, []) := rfl

/-- Wrong-direction messages are dropped too. -/
theorem onMsg_wrong_direction (s : State) (c : Client) (bs : List UInt8) :
    onMsg s c (.output bs) = (s, []) ∧
      onMsg s c (.infoReply bs) = (s, []) ∧
      onMsg s c (.err bs) = (s, []) ∧ onMsg s c .done = (s, []) := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Label removal (pin-the-gaps item 3)

`.labelSet` was pinned four ways — the cap (`onMsg_labels_le`), the round trip
(`Tests/Session.lean`), the forged-record channel (`infoText_records`) and the
boot cap. Its two *removal* siblings were pinned nowhere at all: no theorem, no
fixture, no pty assertion, covered only by the generic cap and by
`Wire.decode_encode`'s ∀-over-`Msg` codec claim. Both arms are unconditional, so
both take the exact-shape treatment `onMsg_screen` gets. -/

/-- **`linger unset <key>` removes exactly the named key.** The exact shape: the
key is the payload through `labelText` (invalid bytes → `""`, which matches no key
`.labelSet` can store since it rejects an empty key), the store is filtered, and
the only effect is `.done`. `rfl`, so a smuggled side effect — a vt touch, a
`.err`, an append — breaks it. -/
theorem onMsg_labelUnset (s : State) (c : Client) (k : List UInt8) :
    onMsg s c (.labelUnset k) =
      ({ s with labels := s.labels.filter (fun kv => kv.1 != labelText k) },
        [.send c.id .done]) := rfl

/-- …and the consequence, stated where a reader looks for it: after an unset, no
label carries that key. This is the promise; the shape above is how it is kept. -/
theorem onMsg_labelUnset_gone (s : State) (c : Client) (k : List UInt8) :
    ∀ kv ∈ (onMsg s c (.labelUnset k)).1.labels, kv.1 ≠ labelText k := by
  intro kv hkv
  simp only [onMsg, List.mem_filter, bne_iff_ne] at hkv
  exact hkv.2

/-- …and it removes *only* that key: every other label survives. Without this,
`onMsg_labelUnset_gone` is satisfied by an arm that clears the whole store — the
vacuity that makes a removal claim worthless. -/
theorem onMsg_labelUnset_keeps (s : State) (c : Client) (k : List UInt8) (kv : String × String)
    (hmem : kv ∈ s.labels) (hne : kv.1 ≠ labelText k) :
    kv ∈ (onMsg s c (.labelUnset k)).1.labels := by
  simp only [onMsg, List.mem_filter, bne_iff_ne]
  exact ⟨hmem, hne⟩

/-- **`linger clear` empties the store, and does nothing else.** -/
theorem onMsg_labelClear (s : State) (c : Client) :
    onMsg s c .labelClear = ({ s with labels := [] }, [.send c.id .done]) := rfl

/-- …the consequence, so the name a reader greps for states the fact. -/
theorem onMsg_labelClear_empty (s : State) (c : Client) :
    (onMsg s c .labelClear).1.labels = [] := rfl

/-! ## §Detach -/

/-- A client vanishing changes nothing but the client list — screen,
scrollback, labels exactly as before — and cannot signal anyone: the
only effect detach may produce is a checkpoint (reboot-resume's save
point when the last attached client leaves). -/
theorem step_closed (s : State) (id : Nat) :
    (step s (.closed id)).1.vt = s.vt ∧
      (step s (.closed id)).1.labels = s.labels ∧
      (step s (.closed id)).2.all (· == .checkpoint) := by
  unfold step
  dsimp only
  split
  · exact ⟨rfl, rfl, by simp⟩
  · exact ⟨rfl, rfl, by simp⟩

/-- With zero clients the mediator still advances, and an owned query still
gets its one child-facing reply; only presentation broadcast disappears. -/
theorem step_ptyOut_no_clients (s : State) (chunk : List UInt8) (h : s.clients = []) :
    step s (.ptyOut chunk) =
      let r := Terminal.feed s.vt s.scan chunk
      ({ s with
          vt := r.vt, scan := r.scan, dirty := true, outSeq := s.outSeq + 1 },
        if r.replies.isEmpty then [] else [Effect.writePty r.replies]) := by
  simp [step, broadcast, h]

/-- With or without clients, the emulator advances identically to `Vt.feed`. -/
theorem step_ptyOut_vt (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.vt = s.vt.feed chunk := by
  simpa [step] using Terminal.feed_vt s.vt s.scan chunk

/-- The one persistent scanner advances exactly once per pty-output event. -/
theorem step_ptyOut_scan (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.scan = (Terminal.feed s.vt s.scan chunk).scan := rfl

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
  unfold broadcast
  split
  · rfl
  · -- every effect a broadcast emits is a `.send`
    induction (s.clients.filter (·.attached)) with
    | nil => rfl
    | cons c cs ih =>
      rw [List.flatMap_cons, List.filter_append, ih, List.append_nil]
      unfold outputMsgs
      rw [List.filter_map]
      simp

/-- The reply prefix depends only on VT, scanner, and bytes; the roster appears
only in the following presentation broadcast. -/
theorem step_ptyOut_effects (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).2 =
      let r := Terminal.feed s.vt s.scan chunk
      (if r.replies.isEmpty then [] else [Effect.writePty r.replies]) ++
        broadcast s r.visible := rfl

/-- **The roster-independence claim, stated over `step` so it can fail.** Two
states that agree on the terminal state but have *arbitrarily different client
rosters* prescribe the same zero-or-one child write. Quantifying over `step`
rather than over `Terminal.feed` is the whole point: an earlier version of this
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
theorem step_childExited_scan (s : State) (status : UInt32) :
    (step s (.childExited status)).1.scan = .ground := by simp [step, Terminal.finish]

/-- The incomplete prefix is the first effect segment, before exited notices,
closes, checkpoint deletion, and daemon exit. -/
theorem step_childExited_effects (s : State) (status : UInt32) :
    (step s (.childExited status)).2 =
      let flushed := Terminal.finish s.scan
      let s' :=
        { s with
          exited := some status, scan := flushed.2 }
      let flush := if flushed.1.isEmpty then [] else broadcast s' flushed.1
      let notify :=
        s'.clients.filter (fun c => c.attached || c.waiting) |>.map
          (fun c => Effect.send c.id (.exited status))
      let closes := s'.clients.map (fun c => Effect.close c.id)
      flush ++ notify ++ closes ++ [.dropCheckpoint, .exit] := rfl

/-- **`detach-all`'s whole purpose, as an equation** (pin-the-gaps item 2). The
verb changes no state at all, so everything it promises lives in the effect
list: one `.close` per *attached* client — the filter is the claim, since a
control connection (`linger send`, `linger info`) must survive a detach-all it
did not ask for — and a `.done` to the requester last, after the closes, so the
caller's own socket is not shut before its reply is queued. `rfl`, so dropping
the filter, reordering the `.done`, or closing the roster instead of the
attached subset each break it.

Before this, the only claim about `.detachAll` was `onMsg_detachAll_vt` below —
the state half of a message whose state half is `s`. -/
theorem onMsg_detachAll (s : State) (c : Client) :
    onMsg s c .detachAll =
      (s,
        (s.clients.filter (·.attached) |>.map (fun c' => Effect.close c'.id)) ++
          [.send c.id .done]) := rfl

/-- `detach-all` closes clients; it cannot touch the screen. Now a corollary of
the full shape above, kept because §Detach's prose cites this weaker name. -/
theorem onMsg_detachAll_vt (s : State) (c : Client) :
    (onMsg s c .detachAll).1 = s := congrArg Prod.fst (onMsg_detachAll s c)

/-- Attach only resizes: the scrollback — the session's history — is
untouched by any attach/detach cycle (observer or not). -/
theorem onMsg_attach_sb (s : State) (c : Client) (cols rows : UInt32) :
    (onMsg s c (.attach cols rows)).1.vt.sb = s.vt.sb := by
  unfold onMsg
  dsimp only
  split
  · simp [State.setClient, Vt.Vt.resize]
  · simp [State.setClient]

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
  unfold onMsg
  dsimp only
  split
  · rename_i h
    exfalso; revert h; simp [State.setClient, hc, hr]
  · simp [State.setClient]

/-- Keystrokes from a full client go to the pty, not the emulator:
echo is the shell's job, so the machine's screen cannot drift. -/
theorem onMsg_input (s : State) (c : Client) (bs : List UInt8)
    (h : ¬(c.attached && !c.sizer) = true) : onMsg s c (.input bs) = (s, [.writePty bs]) := by
  unfold onMsg
  simp [h]

/-- A read-only observer's keyboard goes nowhere (abduco's `-r`):
neither state nor pty sees it. -/
theorem onMsg_input_readonly (s : State) (c : Client) (bs : List UInt8)
    (h : (c.attached && !c.sizer) = true) : onMsg s c (.input bs) = (s, []) := by
  unfold onMsg
  simp [h]

/-! ## §Bound(session) -/

/-- The composite session bound. -/
structure Bounded (s : State) : Prop where
  clientsLe : s.clients.length ≤ maxClients
  labelsLe : s.labels.length ≤ maxLabels
  decOk : ∀ c ∈ s.clients, c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload
  scanOk : s.scan.Bounded

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
theorem step_tick_quiet (s : State) (now : UInt64)
    (h : (s.dirty && decide (now ≥ s.lastCkptMs + ckptIntervalMs)) = false) :
    (step s (.tick now)).2 = [] := by
  unfold step
  dsimp only
  split
  · rename_i hc
    exact absurd (h.symm.trans hc) Bool.false_ne_true
  · rfl

/-- When it does fire: exactly one checkpoint, and **the clock re-arms to `now`** — which is
what makes the cadence a rate rather than a one-time threshold. -/
theorem step_tick_checkpoint (s : State) (now : UInt64)
    (h : (s.dirty && decide (now ≥ s.lastCkptMs + ckptIntervalMs)) = true) :
    (step s (.tick now)).2 = [Effect.checkpoint] ∧ (step s (.tick now)).1.lastCkptMs = now := by
  unfold step
  dsimp only
  rw [ite_eq_left
      (by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; simp [h])]
  exact ⟨rfl, rfl⟩

theorem setClient_length (s : State) (c : Client) :
    (s.setClient c).clients.length = s.clients.length := by simp [State.setClient]

theorem dropClient_length_le (s : State) (id : Nat) :
    (s.dropClient id).clients.length ≤ s.clients.length := by
  simp [State.dropClient]
  exact List.length_filter_le _ _

/-- `onMsg` never grows the client list. -/
theorem onMsg_clients_length_le (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).1.clients.length ≤ s.clients.length := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals simp_all [State.setClient]

/-- `onMsg` keeps labels within the cap. -/
theorem onMsg_labels_le (s : State) (c : Client) (m : Msg) (h : s.labels.length ≤ maxLabels) :
    (onMsg s c m).1.labels.length ≤ maxLabels := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals
    first
    | (simp_all [State.setClient]; done)
    | ( rename_i hguard
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.not_lt] at hguard
        dsimp only
        omega)
    | ( dsimp only
        exact Nat.le_trans (List.length_filter_le _ _) h)

/-- Rewriting one client (same decoder) keeps every stored decoder
healthy. -/
theorem decOk_setClient (s : State) (c0 : Client)
    (hc0 : c0.decoder.errored = false ∧ c0.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h :
      ∀ c' ∈ s.clients, c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload) :
    ∀ c' ∈ (s.setClient c0).clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload := by
  intro c' hmem
  simp only [State.setClient, List.mem_map] at hmem
  obtain ⟨a, ha, heq⟩ := hmem
  by_cases hid : a.id = c0.id
  · simp only [hid, beq_self_eq_true, ite_true] at heq
    subst heq
    exact hc0
  · simp only [hid, not_false_eq_true, ite_eq_right, beq_iff_eq] at heq
    subst heq
    exact h a ha

/-- `onMsg` preserves per-client decoder health: it only ever copies
existing decoders around (attach/resize/wait rewrite other fields). -/
theorem onMsg_decOk (s : State) (c : Client) (m : Msg)
    (hc : c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h :
      ∀ c' ∈ s.clients, c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload) :
    ∀ c' ∈ (onMsg s c m).1.clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals
    first
    | exact h
    | exact decOk_setClient _ _ hc h
    | (intro c' hmem; exact h c' hmem)

theorem onMsg_scan (s : State) (c : Client) (m : Msg) : (onMsg s c m).1.scan = s.scan := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals simp_all [State.setClient]

/-- One message preserves the bound quadruple. -/
theorem onMsg_bounded {s : State} {c : Client} (m : Msg)
    (hc : c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload) (h : Bounded s) :
    Bounded (onMsg s c m).1 :=
  ⟨Nat.le_trans (onMsg_clients_length_le s c m) h.clientsLe, onMsg_labels_le s c m h.labelsLe,
    onMsg_decOk s c m hc h.decOk, by
    rw [onMsg_scan]; exact h.scanOk⟩

theorem client?_mem {s : State} {id : Nat} {c : Client} (h : s.client? id = some c) :
    c ∈ s.clients := List.mem_of_find?_eq_some h

theorem feedMsgs_bounded (id : Nat) (msgs : List Msg) (acc : State × List Effect)
    (h : Bounded acc.1) : Bounded (feedMsgs id msgs acc).1 := by
  induction msgs generalizing acc with
  | nil => exact h
  | cons m ms ih =>
    unfold feedMsgs
    rw [List.foldl_cons]
    rcases hc : acc.1.client? id with - | c'
    · dsimp only [hc]
      exact ih acc h
    · dsimp only [hc]
      exact ih _ (onMsg_bounded m (h.decOk c' (client?_mem hc)) h)

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
        refine ⟨Nat.le_trans (dropClient_length_le s _) hcl, hlb, ?_, hscan⟩
        intro c' hmem
        exact hdec c' ((List.mem_filter.mp hmem).1)
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
    dsimp only
    split
    · refine ⟨Nat.le_trans (dropClient_length_le s _) hcl, hlb, ?_, hscan⟩
      intro c' hmem
      exact hdec c' ((List.mem_filter.mp hmem).1)
    · refine ⟨Nat.le_trans (dropClient_length_le s _) hcl, hlb, ?_, hscan⟩
      intro c' hmem
      exact hdec c' ((List.mem_filter.mp hmem).1)
  · -- ptyOut
    exact ⟨hcl, hlb, hdec, Terminal.feed_bounded _ _ _ hscan⟩
  · -- childExited: finish always returns ground
    exact ⟨hcl, hlb, hdec, Terminal.finish_bounded s.scan⟩
  · -- tick
    split
    · exact ⟨hcl, hlb, hdec, hscan⟩
    · exact ⟨hcl, hlb, hdec, hscan⟩

/-! ## The emulator stays Good through the daemon -/

open Linger.Core.Vt (Good) in
theorem onMsg_vt_good {s : State} {c : Client} (m : Msg) (h : Good s.vt) :
    Good (onMsg s c m).1.vt := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals
    first
    | exact h
    | exact Linger.Core.Vt.Good.resize _ _ (by simpa [State.setClient] using h)
    | simpa [State.setClient] using h

open Linger.Core.Vt (Good) in
theorem feedMsgs_vt_good (id : Nat) (msgs : List Msg) (acc : State × List Effect)
    (h : Good acc.1.vt) : Good (feedMsgs id msgs acc).1.vt := by
  induction msgs generalizing acc with
  | nil => exact h
  | cons m ms ih =>
    unfold feedMsgs
    rw [List.foldl_cons]
    rcases hc : acc.1.client? id with - | c'
    · dsimp only [hc]
      exact ih acc h
    · dsimp only [hc]
      exact ih _ (onMsg_vt_good m h)

open Linger.Core.Vt (Good) in
/-- §Total end-to-end: the screen state a daemon holds stays Good
whatever events arrive — adversarial clients and pty output included. -/
theorem step_vt_good (s : State) (ev : Event) (h : Good s.vt) : Good (step s ev).1.vt := by
  unfold step
  split
  · split
    · exact h
    · exact h
  · split
    · exact h
    · dsimp only
      split
      · exact h
      · apply feedMsgs_vt_good
        simpa [State.setClient] using h
  · dsimp only
    split
    · exact h
    · exact h
  · -- ptyOut
    dsimp only
    rw [Terminal.feed_vt]
    exact Linger.Core.Vt.Good.feed _ h
  · exact h
  · split
    · exact h
    · exact h

end Linger.Core.Session

namespace Linger.Core.Session

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
never a Nat-subtraction lie. The general form was parked when this section
was written ("the `.bytes` case makes it opaque to arithmetic"); the same
`unfold onMsg controlResize` + `repeat' split` script the preservation
theorems use turned out to carry it.
-/

open Linger.Core.Wire (Msg)

/-- Pty output advances the counter by exactly one. -/
theorem outSeq_ptyOut (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.outSeq = s.outSeq + 1 := rfl

/-- Output while somebody is attached is seen as it happens; output with
nobody attached is not. This is the whole mechanism behind `wantsYou`. -/
theorem unseen_ptyOut (s : State) (chunk : List UInt8) (h : s.lookSeq ≤ s.outSeq) :
    unseen (step s (.ptyOut chunk)).1 = !(s.clients.any (·.attached)) := by
  unfold unseen
  show decide ((if s.clients.any (·.attached) then s.outSeq + 1 else s.lookSeq) < s.outSeq + 1) = _
  split
  · simp_all
  · simp_all [Nat.lt_succ_of_le h]

/-- The read mark never overtakes the output counter, so `behind` is honest:
`outSeq - lookSeq` is a real count and never underflows to a misleading zero. -/
theorem lookSeq_le_ptyOut (s : State) (chunk : List UInt8) (h : s.lookSeq ≤ s.outSeq) :
    (step s (.ptyOut chunk)).1.lookSeq ≤ (step s (.ptyOut chunk)).1.outSeq := by
  show (if s.clients.any (·.attached) then s.outSeq + 1 else s.lookSeq) ≤ s.outSeq + 1
  split <;> omega

/-- **A capture is a look** (agent-cli Decision 1). The exact shape: the reply
is `Render.screenText` — the grid, never the ring — chunked and closed with
`.done`, and the ONLY state change is the read mark catching up. `rfl`, so any
smuggled side effect (a vt touch, a label change) breaks it. -/
theorem onMsg_screen (s : State) (c : Client) :
    onMsg s c .screen =
      ({ s with lookSeq := s.outSeq },
        outputMsgs c.id (Render.screenText s.vt) ++ [.send c.id .done]) := rfl

/-- …so after a capture nothing is unseen: "output arrived while nobody was
watching" is false of a session whose screen was just delivered. `.info`
deliberately has no such effect (`ls` polls every daemon), and `.history`
stays an export — the line is drawn at verbs that show the current screen. -/
theorem screen_marks_seen (s : State) (c : Client) : unseen (onMsg s c .screen).1 = false := by
  simp [onMsg, unseen]

/-- …and `behind` counts from the capture: zero at the moment of the look, so
what an agent reads later really is "output events since I captured". -/
theorem screen_behind_zero (s : State) (c : Client) : behind (onMsg s c .screen).1 = 0 := by
  simp [onMsg, behind]

/-- **No client message moves the output counter.** `outSeq` advances only on
`.ptyOut` — real child output — so no connection, whatever it sends, can
forge activity: `unseen`, `fresh` and `behind` can be *caught up* by a look
(attach, capture) but never inflated by traffic. -/
theorem onMsg_outSeq (s : State) (c : Client) (m : Msg) : (onMsg s c m).1.outSeq = s.outSeq := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals simp_all [State.setClient]

/-- The read mark never overtakes the counter through any message: every arm
leaves `lookSeq` alone or catches it up to `outSeq` (attach and capture — the
looks), and none touches `outSeq`. -/
theorem onMsg_lookSeq_le (s : State) (c : Client) (m : Msg) (h : s.lookSeq ≤ s.outSeq) :
    (onMsg s c m).1.lookSeq ≤ (onMsg s c m).1.outSeq := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals
    first
    | simp_all [State.setClient]
    | (simp_all [State.setClient]; omega)

theorem feedMsgs_lookSeq_le (id : Nat) (msgs : List Msg) (acc : State × List Effect)
    (h : acc.1.lookSeq ≤ acc.1.outSeq) :
    (feedMsgs id msgs acc).1.lookSeq ≤ (feedMsgs id msgs acc).1.outSeq := by
  induction msgs generalizing acc with
  | nil => exact h
  | cons m ms ih =>
    unfold feedMsgs
    rw [List.foldl_cons]
    rcases hc : acc.1.client? id with - | c'
    · dsimp only [hc]
      exact ih acc h
    · dsimp only [hc]
      exact ih _ (onMsg_lookSeq_le _ _ _ h)

/-- One event keeps `behind` honest, whatever it is. -/
theorem step_lookSeq_le (s : State) (ev : Event) (h : s.lookSeq ≤ s.outSeq) :
    (step s ev).1.lookSeq ≤ (step s ev).1.outSeq := by
  unfold step
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
    (run s evs).1.lookSeq ≤ (run s evs).1.outSeq := by
  induction evs generalizing s with
  | nil => exact h
  | cons ev evs ih => exact ih (step s ev).1 (step_lookSeq_le s ev h)

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

open Linger.Core.Wire (Msg)

theorem client?_id {s : State} {id : Nat} {c : Client} (h : s.client? id = some c) : c.id = id := by
  have hp := (List.find?_eq_some_iff_append.mp h).1
  simpa using hp

/-- Rewriting one element of a client list cannot change what a lookup
for a *different* id finds. -/
theorem find?_map_set (c : Client) (other : Nat) (hne : other ≠ c.id) :
    ∀ (l : List Client),
      (l.map (fun c' => if c'.id == c.id then c else c')).find? (·.id == other) =
        l.find? (·.id == other)
  | [] => rfl
  | a :: l => by
    have hc : (c.id == other) = false := beq_eq_false_iff_ne.mpr (fun hh => hne hh.symm)
    rw [List.map_cons, List.find?_cons, List.find?_cons]
    by_cases hid : (a.id == c.id) = true
    · have ha : (a.id == other) = false := by
        have : a.id = c.id := by simpa using hid
        exact
          beq_eq_false_iff_ne.mpr
            (by
              rw [this]; exact fun hh => hne hh.symm)
      simp only [hid, ite_true, hc, ha]
      exact find?_map_set c other hne l
    · simp only [hid, Bool.false_eq_true, ite_false]
      cases (a.id == other)
      · exact find?_map_set c other hne l
      · rfl

/-- Dropping one client cannot change what a lookup for a different id
finds. -/
theorem find?_filter_drop (id other : Nat) (hne : other ≠ id) :
    ∀ (l : List Client), (l.filter (·.id != id)).find? (·.id == other) = l.find? (·.id == other)
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons, List.find?_cons]
    by_cases hid : (a.id != id) = true
    · rw [ite_eq_left hid, List.find?_cons]
      cases (a.id == other)
      · exact find?_filter_drop id other hne l
      · rfl
    · have ha : (a.id == other) = false := by
        have : a.id = id := by simpa using hid
        exact
          beq_eq_false_iff_ne.mpr
            (by
              rw [this]; exact fun hh => hne hh.symm)
      rw [ite_eq_right hid]
      simp only [ha]
      exact find?_filter_drop id other hne l

theorem setClient_other {s : State} {c : Client} {other : Nat} (h : other ≠ c.id) :
    (s.setClient c).client? other = s.client? other := find?_map_set c other h s.clients

theorem dropClient_other {s : State} {id other : Nat} (h : other ≠ id) :
    (s.dropClient id).client? other = s.client? other := find?_filter_drop id other h s.clients

/-- One message from `c` leaves every other client's record alone. -/
theorem onMsg_other (s : State) (c : Client) (m : Msg) {other : Nat} (h : other ≠ c.id) :
    (onMsg s c m).1.client? other = s.client? other := by
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals
    first
    | rfl
    | exact setClient_other h

/-- …and so does a whole batch of them. -/
theorem feedMsgs_other (id : Nat) (msgs : List Msg) (acc : State × List Effect) {other : Nat}
    (h : other ≠ id) : (feedMsgs id msgs acc).1.client? other = acc.1.client? other := by
  induction msgs generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    unfold feedMsgs
    rw [List.foldl_cons]
    rcases hc : acc.1.client? id with - | c'
    · dsimp only [hc]
      exact ih acc
    · dsimp only [hc]
      have hstep := ih ((onMsg acc.1 c' m).1, acc.2 ++ (onMsg acc.1 c' m).2)
      unfold feedMsgs at hstep
      rw [hstep]
      exact
        onMsg_other _ _ _
          (by
            rw [client?_id hc]; exact h)

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
    · exact dropClient_other h
    · rw [feedMsgs_other id _ _ h]
      exact
        setClient_other
          (by
            rw [client?_id hfind]; exact h)

end Linger.Core.Session

namespace Linger.Core.Session

/-! ## Trace lift — the per-step theorems over the daemon's whole life

`step`-level preservation says one event is safe; the daemon lives
through millions. `run` names the fold the runtime performs, and these
theorems close the gap: no event *trace* of any length can break the
bounds, corrupt the screen invariant, or let one client's byte stream
touch another's record. Mostly mechanical inductions — the value is the
statement, so the ledger's strongest rows quantify over lifetimes, not
single events.
-/

/-- `run` is exactly the effect-accumulating fold of `step` — state
threading and effect order both. Pins the definition: any deviation
(dropped effects, unthreaded state) breaks this. -/
theorem run_eq_foldl (s : State) (evs : List Event) :
    run s evs =
      evs.foldl
        (fun (acc : State × List Effect) ev => ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2))
        (s, []) := by
  suffices hgen :
    ∀ evs (s : State) (fx : List Effect),
      (fx ++ (run s evs).2 =
          (evs.foldl
              (fun (acc : State × List Effect) ev =>
                ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2))
              (s, fx)).2) ∧
        (run s evs).1 =
          (evs.foldl
              (fun (acc : State × List Effect) ev =>
                ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2))
              (s, fx)).1
    by
    have h := hgen evs s []
    rcases hr : run s evs with ⟨s', fx'⟩
    rw [hr] at h
    simp only [List.nil_append] at h
    rw [Prod.ext_iff]
    exact ⟨h.2, h.1.symm ▸ rfl⟩
  intro evs
  induction evs with
  | nil =>
    intro s fx; simp [run]
  | cons ev evs ih =>
    intro s fx
    have h := ih (step s ev).1 (fx ++ (step s ev).2)
    constructor
    · show fx ++ ((step s ev).2 ++ (run (step s ev).1 evs).2) = _
      rw [List.foldl_cons, ← List.append_assoc]
      exact h.1
    · show (run (step s ev).1 evs).1 = _
      rw [List.foldl_cons]
      exact h.2

/-- The daemon's composite invariant: everything the per-step theorems
preserve, as one predicate. -/
def WF (s : State) : Prop := Bounded s ∧ Linger.Core.Vt.Good s.vt

theorem step_wf (s : State) (ev : Event) (h : WF s) : WF (step s ev).1 :=
  ⟨step_bounded s ev h.1, step_vt_good s ev h.2⟩

/-- §Bound + §Total over the daemon's whole life: no event trace of any
length — adversarial clients, hostile pty bytes, any interleaving — can
break the bounds or the screen invariant. -/
theorem run_wf (s : State) (evs : List Event) (h : WF s) : WF (run s evs).1 := by
  induction evs generalizing s with
  | nil => exact h
  | cons ev evs ih => exact ih (step s ev).1 (step_wf s ev h)

/-- §Isolate over a whole trace: one client's entire byte stream,
however chunked, leaves every other client's record — decoder included
— bit-identical. -/
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other := by
  induction chunks generalizing s with
  | nil => rfl
  | cons c cs
    ih =>
    show (run (step s (.bytes id c)).1 (cs.map (Event.bytes id))).1.client? other = _
    rw [ih (step s (.bytes id c)).1]
    exact step_bytes_isolates s id c h

end Linger.Core.Session

namespace Linger.Core.Session

/-! ## §Renderable lifted to the daemon's whole life

The emulator-level invariant is only useful if the *daemon's* terminal satisfies
it, for any event trace. A session does exactly three things to its `Vt`: feeds
it pty bytes (through the mediator, whose VT projection is `Vt.feed` —
`Terminal.feed_vt`), resizes it on attach or resize, and nothing else. Those are
precisely `LiveReachableVt`'s constructors, so the lift is an induction with no
new content — which is the point: the replay theorem may assume a *reachable*
grid without that assumption smuggling in a side condition.
-/

open Linger.Core.Wire (Msg)
open Linger.Core.Vt (LiveReachableVt Renderable)

/-- The daemon's terminal is one a live session can hold. -/
def LiveVt (s : State) : Prop := LiveReachableVt s.vt

theorem onMsg_vt_live {s : State} {c : Client} (m : Msg) (h : LiveVt s) :
    LiveVt (onMsg s c m).1 := by
  unfold LiveVt at h ⊢
  unfold onMsg controlResize
  dsimp only
  repeat' split
  all_goals
    first
    | exact h
    | exact LiveReachableVt.resize (by simpa [State.setClient] using h) _ _
    | simpa [State.setClient] using h

theorem feedMsgs_vt_live (id : Nat) (msgs : List Msg) (acc : State × List Effect)
    (h : LiveVt acc.1) : LiveVt (feedMsgs id msgs acc).1 := by
  induction msgs generalizing acc with
  | nil => exact h
  | cons m ms ih =>
    unfold feedMsgs
    rw [List.foldl_cons]
    rcases hc : acc.1.client? id with - | c'
    · dsimp only [hc]
      exact ih acc h
    · dsimp only [hc]
      exact ih _ (onMsg_vt_live m h)

/-- One event keeps the terminal reachable. -/
theorem step_vt_live (s : State) (ev : Event) (h : LiveVt s) : LiveVt (step s ev).1 := by
  unfold LiveVt at h ⊢
  unfold step
  split
  · split
    · exact h
    · exact h
  · split
    · exact h
    · dsimp only
      split
      · exact h
      · refine feedMsgs_vt_live _ _ _ ?_
        show LiveReachableVt _
        simpa [State.setClient] using h
  · dsimp only
    split
    · exact h
    · exact h
  · -- pty output: the mediator's VT projection is exactly `Vt.feed`
    dsimp only
    rw [Terminal.feed_vt]
    exact LiveReachableVt.feed h _
  · exact h
  · split
    · exact h
    · exact h

/-- …and so does a trace of any length. -/
theorem run_vt_live (s : State) (evs : List Event) (h : LiveVt s) : LiveVt (run s evs).1 := by
  induction evs generalizing s with
  | nil => exact h
  | cons ev evs ih =>
    show LiveVt (run (step s ev).1 evs).1
    exact ih _ (step_vt_live s ev h)

/-- **The shape hypothesis, discharged at the daemon level.** Whatever a session
has been through — adversarial clients, hostile pty bytes, resizes, any
interleaving — the grid it holds is one `Render.restore` can express. -/
theorem run_vt_renderable (s : State) (evs : List Event) (h : LiveVt s) :
    Renderable (run s evs).1.vt := Linger.Core.Vt.renderable_of_liveReachable (run_vt_live s evs h)

/-- A daemon booting from a fresh emulator satisfies the hypothesis, so the
statement above is not conditional in practice. -/
theorem liveVt_init (cols rows : Nat) (cs : List Client) (ls : List (String × String)) :
    LiveVt { vt := Vt.Vt.init cols rows, clients := cs, labels := ls } :=
  LiveReachableVt.init cols rows

/-- …and stated through the one door the runtime actually walks through. -/
theorem liveVt_boot (cols rows : Nat) (ls mk : List (String × String)) :
    LiveVt (State.boot (Vt.Vt.init cols rows) ls mk) := LiveReachableVt.init cols rows

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

theorem boot_wf (vt : Vt.Vt) (labels metaKv : List (String × String)) (h : Linger.Core.Vt.Good vt) :
    WF (State.boot vt labels metaKv) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, h⟩
  · show ([] : List Client).length ≤ maxClients
    simp [maxClients]
  · show (labels.take maxLabels).length ≤ maxLabels
    rw [List.length_take]
    exact Nat.min_le_left _ _
  · intro c hc
    exact absurd hc (List.not_mem_nil)
  · show Terminal.Scan.Bounded .ground
    trivial

/-- **The A2 anchor made structural**: every state reachable from any boot —
which, by the seal, is every state the daemon can possess — is well-formed,
whatever the trace: adversarial clients, hostile pty bytes, forged
checkpoints' label lists, any interleaving. -/
theorem run_boot_wf (vt : Vt.Vt) (labels metaKv : List (String × String)) (evs : List Event)
    (h : Linger.Core.Vt.Good vt) :
    WF (run (State.boot vt labels metaKv) evs).1 := run_wf _ _ (boot_wf vt labels metaKv h)

/-- **Only the size owner resizes the pty** (abduco's rule, as a theorem rather than
a comment). `resizeEffects` emits a `resizePty` only for the client the size-ownership
cascade (`sizeOwner`: newest attached real-terminal attacher) actually selected — a
read-only observer or an older mirror never moves the pty out from under the active
user. -/
theorem resizeEffects_owner_only (s : State) (c : Client) :
    resizeEffects s c ≠ [] → (sizeOwner s).any (·.id == c.id) = true := by
  intro hne
  by_cases hc : (sizeOwner s).any (·.id == c.id) = true
  · exact hc
  · exact
      absurd
        (by
          unfold resizeEffects; rw [ite_eq_right hc])
        hne

/-- …and when it does resize, it is exactly one `resizePty` at the client's size —
never a burst, never a stale size. -/
theorem resizeEffects_atMostOne (s : State) (c : Client) :
    resizeEffects s c = [] ∨ resizeEffects s c = [Effect.resizePty c.cols c.rows] := by
  unfold resizeEffects; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## §Size — a control resize never overrides an attached sizer

`linger resize` (agent-cli Decision 3) lets an agent size a *detached* session
so wrap is deterministic before a capture. The abduco rule extends rather than
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
at the requested size, the emulator resized with it, then `.done`. -/
theorem controlResize_applies (s : State) (c : Client) (cols rows : UInt32)
    (hown : (sizeOwner s).isSome = false) (hnz : (cols == 0 || rows == 0) = false)
    (hdiff : (s.vt.cols == cols.toNat && s.vt.rows == rows.toNat) = false) :
    controlResize s c cols rows =
      ({ s with vt := s.vt.resize cols.toNat rows.toNat },
        [.resizePty cols rows, .send c.id .done]) := by
  unfold controlResize
  rw [ite_eq_right (by simp [hown]), ite_eq_right (by simp [hnz]), ite_eq_right (by simp [hdiff])]

/-- The same-size branch is inert on purpose: the emulator — scroll region and
tab ruler included — is untouched (`Vt.resize` would wipe both and no SIGWINCH
re-establishes them at an unchanged winsize; the attach guard's reason), and
the reply is still `.done`: idempotent success, the pty already IS that size. -/
theorem controlResize_same_size (s : State) (c : Client) (cols rows : UInt32)
    (hown : (sizeOwner s).isSome = false) (hnz : (cols == 0 || rows == 0) = false)
    (hsame : (s.vt.cols == cols.toNat && s.vt.rows == rows.toNat) = true) :
    controlResize s c cols rows = (s, [.send c.id .done]) := by
  unfold controlResize
  rw [ite_eq_right (by simp [hown]), ite_eq_right (by simp [hnz]), ite_eq_left hsame]

/-- The `.resize` arm routes every non-attached connection to the stage above
(after the cols/rows bookkeeping on the client record), so the three claims
are about what the daemon actually runs. -/
theorem onMsg_resize_control (s : State) (c : Client) (cols rows : UInt32)
    (hc : c.attached = false) :
    onMsg s c (.resize cols rows) =
      controlResize
        (s.setClient
          { c with
            cols, rows })
        { c with
          cols, rows }
        cols rows := by
  unfold onMsg
  simp [hc]

/-- **Every control resize answers the requester** — `.done` or `.err`, never
silence. The three shape theorems above each show a reply *under their guard*;
this is the guard-free totality that makes the reply a contract: the branches
are exhaustive, so a future branch that silently drops (the attached path's
`(s, [])` shape) cannot appear here without failing this. It is the pure half
of the no-hang story — `Client.drainBounded` owns the other half, against
daemons that predate the verb entirely. -/
theorem controlResize_replies (s : State) (c : Client) (cols rows : UInt32) :
    (controlResize s c cols rows).2.any
        (fun e =>
          match e with
          | .send i .done => i == c.id
          | .send i (.err _) => i == c.id
          | _ => false) =
      true := by
  unfold controlResize
  repeat' split
  all_goals simp

end Linger.Core.Session

namespace Linger.Core.Session

open Linger.Core.Vt

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
`Linger/Core/Render.lean`'s header makes, and the reason `Render.history` is still only
*bounded* rather than proved (`tests/coverage.py`). `infoText` now builds
`List UInt8` directly. -/

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
  unfold infoText at hb
  simp only [List.mem_flatMap] at hb
  obtain ⟨kv, -, hmem⟩ := hb
  rcases List.mem_append.mp hmem with h | h
  · rcases List.mem_append.mp h with h' | h'
    · rcases List.mem_append.mp h' with h'' | h''
      · exact Or.inr (Or.inr (Render.utf8s_no_ctl _ b h''))
      · simp only [List.mem_singleton] at h''
        exact Or.inl h''
    · exact Or.inr (Or.inr (Render.utf8s_no_ctl _ b h'))
  · simp only [List.mem_singleton] at h
    exact Or.inr (Or.inl h)

private theorem count_utf8s_frame (cs : List Char) (b : UInt8) (hb : b = 0x09 ∨ b = 0x0A) :
    (Render.utf8s cs).count b = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  obtain ⟨h9, h10⟩ := utf8s_no_frame cs b hmem
  rcases hb with h | h
  · exact h9 h
  · exact h10 h

private theorem count_frame :
    ∀ (l : List (String × String)) (b : UInt8),
      b = 0x09 ∨ b = 0x0A →
        (l.flatMap
                (fun kv =>
                  Render.utf8s kv.1.toList ++ [0x09] ++ Render.utf8s kv.2.toList ++ [0x0A])).count
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

end Linger.Core.Session

namespace Linger.Core.Session

open Linger.Core.Wire (Msg)

/-! ## §Chunk at the session layer — what a client receives is what was sent

A3 says the *transport* is invisible: any re-chunking of an encoded stream decodes to
exactly that stream. The session does its own framing on top of that — `outputMsgs`
splits a payload into ≤ 64 KiB `output` frames — and that framing had no claim at all.
`chunksOf`, the function that does it, appeared in `Theorems/` exactly once, in a
comment; it is the same blindness in the old coverage gate that let `infoText` pass.

Two claims, and they are the two properties the runtime depends on: the split loses
nothing (so a reattaching client's repaint is complete) and no frame exceeds the cap
(so `Wire`'s §Bound well-formedness holds of what the daemon actually sends). -/

/-! `chunksOf` recurses on `l.drop n` under a well-founded measure. Rather than
re-supply its `decreasing_by`, both proofs below induct on a length *bound* — the
standard trick, and it keeps them Mathlib-free. -/

private theorem chunksOf_flatten_aux {α : Type} (n : Nat) :
    ∀ (k : Nat) (l : List α), l.length ≤ k → (chunksOf n l).flatten = l := by
  intro k
  induction k with
  | zero =>
    intro l hl
    cases l with
    | nil =>
      unfold chunksOf
      split
      · simp
      · rename_i h
        exact absurd (Or.inl (by simp : ([] : List α).length ≤ n)) h
    | cons a t => simp at hl
  | succ k ih =>
    intro l hl
    unfold chunksOf
    split
    · simp
    · rename_i h
      have hn0 : n ≠ 0 := fun hz => h (Or.inr hz)
      have hgt : n < l.length := Nat.lt_of_not_le (fun hle => h (Or.inl hle))
      simp only [List.flatten_cons]
      rw [ih (l.drop n)
          (by
            simp only [List.length_drop]; omega)]
      exact List.take_append_drop n l

theorem chunksOf_flatten {α : Type} (n : Nat) (l : List α) : (chunksOf n l).flatten = l :=
  chunksOf_flatten_aux n l.length l (Nat.le_refl _)

private theorem chunksOf_le_aux {α : Type} (n : Nat) (hn : 0 < n) :
    ∀ (k : Nat) (l : List α), l.length ≤ k → ∀ c ∈ chunksOf n l, c.length ≤ n := by
  intro k
  induction k with
  | zero =>
    intro l hl
    cases l with
    | nil =>
      unfold chunksOf
      split
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        simp
      · rename_i h
        exact absurd (Or.inl (by simp : ([] : List α).length ≤ n)) h
    | cons a t => simp at hl
  | succ k ih =>
    intro l hl
    unfold chunksOf
    split
    · rename_i h
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      rcases h with h | h
      · exact h
      · omega
    · rename_i h
      have hn0 : n ≠ 0 := fun hz => h (Or.inr hz)
      have hgt : n < l.length := Nat.lt_of_not_le (fun hle => h (Or.inl hle))
      intro c hc
      rcases List.mem_cons.mp hc with hh | hh
      · subst hh
        simp only [List.length_take]
        omega
      · exact
          ih (l.drop n)
            (by
              simp only [List.length_drop]; omega)
            c hh

theorem chunksOf_le {α : Type} (n : Nat) (hn : 0 < n) (l : List α) :
    ∀ c ∈ chunksOf n l, c.length ≤ n := chunksOf_le_aux n hn l.length l (Nat.le_refl _)

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
  unfold outputMsgs
  induction chunksOf outputChunk bs with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.filterMap_cons]; simpa using ih

/-- **The session's framing loses nothing.** Concatenating the payloads of the frames
`outputMsgs` produces gives back exactly the bytes it was handed — so the repaint a
reattaching client receives is the whole of `Render.restore`, not a prefix of it. -/
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

end Linger.Core.Session
