import Zmx.Core.Session
import Theorems.Wire
import Theorems.Vt
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

/-- A client vanishing changes nothing but the client list — the
screen, scrollback, labels are exactly as before, and nothing else
happens. Detach is free. -/
theorem step_closed (s : State) (id : Nat) :
    (step s (.closed id)).1.vt = s.vt ∧
    (step s (.closed id)).1.labels = s.labels ∧
    (step s (.closed id)).2 = [] := by
  refine ⟨rfl, rfl, rfl⟩

/-- The session with zero clients still advances: pty output reaches
the emulator exactly as it would with clients (broadcast just has no
recipients). This is what makes reattach-after-a-week work. -/
theorem step_ptyOut_no_clients (s : State) (chunk : List UInt8)
    (h : s.clients = []) :
    step s (.ptyOut chunk)
      = ({ s with vt := s.vt.feed chunk, dirty := true }, []) := by
  simp [step, broadcast, h]

/-- With or without clients, the emulator advances identically. -/
theorem step_ptyOut_vt (s : State) (chunk : List UInt8) :
    (step s (.ptyOut chunk)).1.vt = s.vt.feed chunk := rfl

/-- `detach-all` closes clients; it cannot touch the screen. -/
theorem onMsg_detachAll_vt (s : State) (c : Client) :
    (onMsg s c .detachAll).1 = s := rfl

/-- Attach only resizes: the scrollback — the session's history — is
untouched by any attach/detach cycle. -/
theorem onMsg_attach_sb (s : State) (c : Client) (cols rows : UInt32) :
    (onMsg s c (.attach cols rows)).1.vt.sb = s.vt.sb := by
  simp [onMsg, State.setClient, Vt.Vt.resize]

/-- Keystrokes go to the pty, not the emulator: echo is the shell's
job, so the machine's screen cannot drift from the real one. -/
theorem onMsg_input (s : State) (c : Client) (bs : List UInt8) :
    onMsg s c (.input bs) = (s, [.writePty bs]) := rfl

/-! ## §Bound(session) -/

/-- The composite session bound. -/
structure Bounded (s : State) : Prop where
  clientsLe : s.clients.length ≤ maxClients
  labelsLe : s.labels.length ≤ maxLabels
  decOk : ∀ c ∈ s.clients,
    c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload

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

/-- One message preserves the bound triple. -/
theorem onMsg_bounded {s : State} {c : Client} (m : Msg)
    (hc : c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload)
    (h : Bounded s) : Bounded (onMsg s c m).1 :=
  ⟨Nat.le_trans (onMsg_clients_length_le s c m) h.clientsLe,
   onMsg_labels_le s c m h.labelsLe,
   onMsg_decOk s c m hc h.decOk⟩

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
list, the label table, or any client's decoder past their caps. -/
theorem step_bounded (s : State) (ev : Event) (h : Bounded s) :
    Bounded (step s ev).1 := by
  obtain ⟨hcl, hlb, hdec⟩ := h
  have h' : Bounded s := ⟨hcl, hlb, hdec⟩
  unfold step
  split
  · -- connected
    split
    · exact h'
    · rename_i hlt
      refine ⟨?_, hlb, ?_⟩
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
        refine ⟨Nat.le_trans (dropClient_length_le s _) hcl, hlb, ?_⟩
        intro c' hmem
        exact hdec c' ((List.mem_filter.mp hmem).1)
      · rename_i herr
        apply feedMsgs_bounded
        dsimp only
        have hcmem := client?_mem hfind
        have hcok := hdec c hcmem
        -- the new decoder is healthy: not errored (guard) and capped
        refine ⟨?_, hlb, ?_⟩
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
  · -- closed
    refine ⟨Nat.le_trans (dropClient_length_le s _) hcl, hlb, ?_⟩
    intro c' hmem
    exact hdec c' ((List.mem_filter.mp hmem).1)
  · -- ptyOut
    exact ⟨hcl, hlb, hdec⟩
  · -- childExited
    exact ⟨hcl, hlb, hdec⟩
  · -- tick
    split
    · exact ⟨hcl, hlb, hdec⟩
    · exact h'

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
  · exact h
  · exact Zmx.Core.Vt.Good.feed _ h
  · exact h
  · split
    · exact h
    · exact h

end Zmx.Core.Session
