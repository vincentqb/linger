import Zmx.Core.Session
import Theorems.Wire
import Theorems.Vt
import Theorems.Terminal
/-! # §Detach / §Bound(session) — the daemon state machine theorems

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

namespace Zmx.Core.Session

open Zmx.Core.Wire (Msg)

/-! ## §Frame (machine half) and other exact-shape facts -/

theorem onMsg_unknown (s : State) (c : Client) (t : UInt8) (p : List UInt8) :
    onMsg s c (.unknown t p) = (s, []) := rfl

/-- Wrong-direction messages are dropped too. -/
theorem onMsg_wrong_direction (s : State) (c : Client) (bs : List UInt8) :
    onMsg s c (.output bs) = (s, []) ∧ onMsg s c (.infoReply bs) = (s, []) ∧
    onMsg s c (.err bs) = (s, []) ∧ onMsg s c .done = (s, []) :=
  ⟨rfl, rfl, rfl, rfl⟩

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
theorem step_ptyOut_no_clients (s : State) (chunk : List UInt8)
    (h : s.clients = []) :
    step s (.ptyOut chunk) =
      let r := Terminal.feed s.vt s.scan chunk
      ({ s with vt := r.vt, scan := r.scan, dirty := true,
                  outSeq := s.outSeq + 1 },
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
what makes the reply channel and the presentation channel separable. -/theorem broadcast_no_writePty (s : State) (bytes : List UInt8) :
    (broadcast s bytes).filter (fun e => match e with
        | .writePty _ => true
        | _ => false) = [] := by
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
theorem ptyOut_reply_roster_independent (s t : State) (chunk : List UInt8)
    (hv : s.vt = t.vt) (hs : s.scan = t.scan) :
    (step s (.ptyOut chunk)).2.filter (fun e => match e with
        | .writePty _ => true
        | _ => false)
      = (step t (.ptyOut chunk)).2.filter (fun e => match e with
        | .writePty _ => true
        | _ => false) := by
  rw [step_ptyOut_effects, step_ptyOut_effects]
  dsimp only
  rw [hv, hs]
  -- the presentation broadcast contributes no child write, whatever the roster
  rw [List.filter_append, List.filter_append, broadcast_no_writePty,
    broadcast_no_writePty]

/-- Child exit resets the scanner; `finish`'s pending bytes are broadcast by
`step` before exited notifications and close effects. -/
theorem step_childExited_scan (s : State) (status : UInt32) :
    (step s (.childExited status)).1.scan = .ground := by
  simp [step, Terminal.finish]

/-- The incomplete prefix is the first effect segment, before exited notices,
closes, checkpoint deletion, and daemon exit. -/
theorem step_childExited_effects (s : State) (status : UInt32) :
    (step s (.childExited status)).2 =
      let flushed := Terminal.finish s.scan
      let s' := { s with exited := some status, scan := flushed.2 }
      let flush := if flushed.1.isEmpty then [] else broadcast s' flushed.1
      let notify := s'.clients.filter (fun c => c.attached || c.waiting)
        |>.map (fun c => Effect.send c.id (.exited status))
      let closes := s'.clients.map (fun c => Effect.close c.id)
      flush ++ notify ++ closes ++ [.dropCheckpoint, .exit] := rfl

/-- `detach-all` closes clients; it cannot touch the screen. -/
theorem onMsg_detachAll_vt (s : State) (c : Client) :
    (onMsg s c .detachAll).1 = s := rfl

/-- Attach only resizes: the scrollback — the session's history — is
untouched by any attach/detach cycle (observer or not). -/
theorem onMsg_attach_sb (s : State) (c : Client) (cols rows : UInt32) :
    (onMsg s c (.attach cols rows)).1.vt.sb = s.vt.sb := by
  unfold onMsg
  dsimp only
  split
  · simp [State.setClient, Vt.Vt.resize]
  · simp [State.setClient]

/-- Keystrokes from a full client go to the pty, not the emulator:
echo is the shell's job, so the machine's screen cannot drift. -/
theorem onMsg_input (s : State) (c : Client) (bs : List UInt8)
    (h : ¬(c.attached && !c.sizer) = true) :
    onMsg s c (.input bs) = (s, [.writePty bs]) := by
  unfold onMsg
  simp [h]

/-- A read-only observer's keyboard goes nowhere (abduco's `-r`):
neither state nor pty sees it. -/
theorem onMsg_input_readonly (s : State) (c : Client) (bs : List UInt8)
    (h : (c.attached && !c.sizer) = true) :
    onMsg s c (.input bs) = (s, []) := by
  unfold onMsg
  simp [h]

/-! ## §Bound(session) -/

/-- The composite session bound. -/
structure Bounded (s : State) : Prop where
  clientsLe : s.clients.length ≤ maxClients
  labelsLe : s.labels.length ≤ maxLabels
  decOk : ∀ c ∈ s.clients,
    c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload
  scanOk : s.scan.Bounded

theorem setClient_length (s : State) (c : Client) :
    (s.setClient c).clients.length = s.clients.length := by
  simp [State.setClient]

theorem dropClient_length_le (s : State) (id : Nat) :
    (s.dropClient id).clients.length ≤ s.clients.length := by
  simp [State.dropClient]
  exact List.length_filter_le _ _

/-- `onMsg` never grows the client list. -/
theorem onMsg_clients_length_le (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).1.clients.length ≤ s.clients.length := by
  unfold onMsg
  dsimp only
  repeat' split
  all_goals simp_all [State.setClient]

/-- `onMsg` keeps labels within the cap. -/
theorem onMsg_labels_le (s : State) (c : Client) (m : Msg)
    (h : s.labels.length ≤ maxLabels) :
    (onMsg s c m).1.labels.length ≤ maxLabels := by
  unfold onMsg
  dsimp only
  repeat' split
  all_goals first
    | (simp_all [State.setClient]; done)
    | (rename_i hguard
       simp only [List.length_append, List.length_cons, List.length_nil,
         Nat.not_lt] at hguard
       dsimp only
       omega)
    | (dsimp only
       exact Nat.le_trans (List.length_filter_le _ _) h)

/-- Rewriting one client (same decoder) keeps every stored decoder
healthy. -/
theorem decOk_setClient (s : State) (c0 : Client)
    (hc0 : c0.decoder.errored = false ∧ c0.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h : ∀ c' ∈ s.clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload) :
    ∀ c' ∈ (s.setClient c0).clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload := by
  intro c' hmem
  simp only [State.setClient, List.mem_map] at hmem
  obtain ⟨a, ha, heq⟩ := hmem
  by_cases hid : a.id = c0.id
  · simp only [hid, beq_self_eq_true, if_true] at heq
    subst heq
    exact hc0
  · simp only [hid, not_false_eq_true, if_neg, beq_iff_eq] at heq
    subst heq
    exact h a ha

/-- `onMsg` preserves per-client decoder health: it only ever copies
existing decoders around (attach/resize/wait rewrite other fields). -/
theorem onMsg_decOk (s : State) (c : Client) (m : Msg)
    (hc : c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h : ∀ c' ∈ s.clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload) :
    ∀ c' ∈ (onMsg s c m).1.clients,
      c'.decoder.errored = false ∧ c'.decoder.buf.length ≤ 4 + Wire.maxPayload := by
  unfold onMsg
  dsimp only
  repeat' split
  all_goals first
    | exact h
    | exact decOk_setClient _ _ hc h
    | (intro c' hmem; exact h c' hmem)

theorem onMsg_scan (s : State) (c : Client) (m : Msg) :
    (onMsg s c m).1.scan = s.scan := by
  unfold onMsg
  dsimp only
  repeat' split
  all_goals simp_all [State.setClient]

/-- One message preserves the bound quadruple. -/
theorem onMsg_bounded {s : State} {c : Client} (m : Msg)
    (hc : c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h : Bounded s) : Bounded (onMsg s c m).1 :=
  ⟨Nat.le_trans (onMsg_clients_length_le s c m) h.clientsLe,
   onMsg_labels_le s c m h.labelsLe,
   onMsg_decOk s c m hc h.decOk,
   by rw [onMsg_scan]; exact h.scanOk⟩

theorem client?_mem {s : State} {id : Nat} {c : Client}
    (h : s.client? id = some c) : c ∈ s.clients :=
  List.mem_of_find?_eq_some h

theorem feedMsgs_bounded (id : Nat) (msgs : List Msg)
    (acc : State × List Effect) (h : Bounded acc.1) :
    Bounded (feedMsgs id msgs acc).1 := by
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
theorem step_bounded (s : State) (ev : Event) (h : Bounded s) :
    Bounded (step s ev).1 := by
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
            have := Wire.Decoder.feed_buf_le c.decoder chunk
              (by simp [hcok.1])
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

open Zmx.Core.Vt (Good) in
theorem onMsg_vt_good {s : State} {c : Client} (m : Msg)
    (h : Good s.vt) : Good (onMsg s c m).1.vt := by
  unfold onMsg
  dsimp only
  repeat' split
  all_goals first
    | exact h
    | exact Zmx.Core.Vt.Good.resize _ _ (by simpa [State.setClient] using h)
    | simpa [State.setClient] using h

open Zmx.Core.Vt (Good) in
theorem feedMsgs_vt_good (id : Nat) (msgs : List Msg)
    (acc : State × List Effect) (h : Good acc.1.vt) :
    Good (feedMsgs id msgs acc).1.vt := by
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

open Zmx.Core.Vt (Good) in
/-- §Total end-to-end: the screen state a daemon holds stays Good
whatever events arrive — adversarial clients and pty output included. -/
theorem step_vt_good (s : State) (ev : Event) (h : Good s.vt) :
    Good (step s ev).1.vt := by
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
    exact Zmx.Core.Vt.Good.feed _ h
  · exact h
  · split
    · exact h
    · exact h

end Zmx.Core.Session



namespace Zmx.Core.Session
/-! ## §Unread — the output counter

`unseen` is "output arrived while nobody was watching", and it is a property
of the **session**: `lookSeq` catches up on attach and on every output that
happens while somebody is attached, so a one-off connection from a stranger
creates no per-client state. A counter rather than a timestamp because it is
determined by the event list alone.

Scope of what is proved here: the two claims about the event that *writes*
the counters. The general `∀ ev` versions need an induction showing
`feedMsgs` preserves `outSeq` (client messages never touch it), which the
`.bytes` case makes opaque to arithmetic; recorded in SCRATCHPAD as the next
increment rather than asserted here.
-/

/-- Pty output advances the counter by exactly one. -/
theorem outSeq_ptyOut (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.outSeq = s.outSeq + 1 := rfl

/-- Output while somebody is attached is seen as it happens; output with
nobody attached is not. This is the whole mechanism behind `wantsYou`. -/
theorem unseen_ptyOut (s : State) (chunk : List UInt8) (h : s.lookSeq ≤ s.outSeq) :
    unseen (step s (.ptyOut chunk)).1 = !(s.clients.any (·.attached)) := by
  unfold unseen
  show decide ((if s.clients.any (·.attached) then s.outSeq + 1 else s.lookSeq)
      < s.outSeq + 1) = _
  split
  · simp_all
  · simp_all [Nat.lt_succ_of_le h]

/-- The read mark never overtakes the output counter, so `behind` is honest:
`outSeq - lookSeq` is a real count and never underflows to a misleading zero. -/
theorem lookSeq_le_ptyOut (s : State) (chunk : List UInt8)
    (h : s.lookSeq ≤ s.outSeq) :
    (step s (.ptyOut chunk)).1.lookSeq ≤ (step s (.ptyOut chunk)).1.outSeq := by
  show (if s.clients.any (·.attached) then s.outSeq + 1 else s.lookSeq) ≤ s.outSeq + 1
  split <;> omega

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

open Zmx.Core.Wire (Msg)

theorem client?_id {s : State} {id : Nat} {c : Client}
    (h : s.client? id = some c) : c.id = id := by
  have hp := (List.find?_eq_some_iff_append.mp h).1
  simpa using hp

/-- Rewriting one element of a client list cannot change what a lookup
for a *different* id finds. -/
theorem find?_map_set (c : Client) (other : Nat) (hne : other ≠ c.id) :
    ∀ (l : List Client),
      (l.map (fun c' => if c'.id == c.id then c else c')).find? (·.id == other)
        = l.find? (·.id == other)
  | [] => rfl
  | a :: l => by
    have hc : (c.id == other) = false :=
      beq_eq_false_iff_ne.mpr (fun hh => hne hh.symm)
    rw [List.map_cons, List.find?_cons, List.find?_cons]
    by_cases hid : (a.id == c.id) = true
    · have ha : (a.id == other) = false := by
        have : a.id = c.id := by simpa using hid
        exact beq_eq_false_iff_ne.mpr (by rw [this]; exact fun hh => hne hh.symm)
      simp only [hid, if_true, hc, ha]
      exact find?_map_set c other hne l
    · simp only [hid, Bool.false_eq_true, if_false]
      cases (a.id == other)
      · exact find?_map_set c other hne l
      · rfl

/-- Dropping one client cannot change what a lookup for a different id
finds. -/
theorem find?_filter_drop (id other : Nat) (hne : other ≠ id) :
    ∀ (l : List Client),
      (l.filter (·.id != id)).find? (·.id == other) = l.find? (·.id == other)
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons, List.find?_cons]
    by_cases hid : (a.id != id) = true
    · rw [if_pos hid, List.find?_cons]
      cases (a.id == other)
      · exact find?_filter_drop id other hne l
      · rfl
    · have ha : (a.id == other) = false := by
        have : a.id = id := by simpa using hid
        exact beq_eq_false_iff_ne.mpr (by rw [this]; exact fun hh => hne hh.symm)
      rw [if_neg hid]
      simp only [ha]
      exact find?_filter_drop id other hne l

theorem setClient_other {s : State} {c : Client} {other : Nat} (h : other ≠ c.id) :
    (s.setClient c).client? other = s.client? other :=
  find?_map_set c other h s.clients

theorem dropClient_other {s : State} {id other : Nat} (h : other ≠ id) :
    (s.dropClient id).client? other = s.client? other :=
  find?_filter_drop id other h s.clients

/-- One message from `c` leaves every other client's record alone. -/
theorem onMsg_other (s : State) (c : Client) (m : Msg) {other : Nat}
    (h : other ≠ c.id) :
    (onMsg s c m).1.client? other = s.client? other := by
  unfold onMsg
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | exact setClient_other h

/-- …and so does a whole batch of them. -/
theorem feedMsgs_other (id : Nat) (msgs : List Msg) (acc : State × List Effect)
    {other : Nat} (h : other ≠ id) :
    (feedMsgs id msgs acc).1.client? other = acc.1.client? other := by
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
      exact onMsg_other _ _ _ (by rw [client?_id hc]; exact h)

/-- §Isolate: bytes from one client cannot alter another client's
record — including its wire decoder, so a peer stuck mid-frame stays
mid-frame and resumes correctly on its next chunk. Daemon-level
concurrency safety is this, plus §Chunk (per-connection ordering),
plus single-threadedness. -/
theorem step_bytes_isolates (s : State) (id : Nat) (chunk : List UInt8)
    {other : Nat} (h : other ≠ id) :
    (step s (.bytes id chunk)).1.client? other = s.client? other := by
  unfold step
  dsimp only
  split
  · rfl
  · rename_i c hfind
    split
    · exact dropClient_other h
    · rw [feedMsgs_other id _ _ h]
      exact setClient_other (by rw [client?_id hfind]; exact h)

end Zmx.Core.Session



namespace Zmx.Core.Session
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
    run s evs = evs.foldl
      (fun (acc : State × List Effect) ev =>
        ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2))
      (s, []) := by
  suffices hgen : ∀ evs (s : State) (fx : List Effect),
      (fx ++ (run s evs).2 = (evs.foldl
        (fun (acc : State × List Effect) ev =>
          ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2)) (s, fx)).2)
      ∧ (run s evs).1 = (evs.foldl
        (fun (acc : State × List Effect) ev =>
          ((step acc.1 ev).1, acc.2 ++ (step acc.1 ev).2)) (s, fx)).1 by
    have h := hgen evs s []
    rcases hr : run s evs with ⟨s', fx'⟩
    rw [hr] at h
    simp only [List.nil_append] at h
    rw [Prod.ext_iff]
    exact ⟨h.2, h.1.symm ▸ rfl⟩
  intro evs
  induction evs with
  | nil => intro s fx; simp [run]
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
def WF (s : State) : Prop := Bounded s ∧ Zmx.Core.Vt.Good s.vt

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
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8))
    {other : Nat} (h : other ≠ id) :
    (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other := by
  induction chunks generalizing s with
  | nil => rfl
  | cons c cs ih =>
    show (run (step s (.bytes id c)).1 (cs.map (Event.bytes id))).1.client? other = _
    rw [ih (step s (.bytes id c)).1]
    exact step_bytes_isolates s id c h

end Zmx.Core.Session
