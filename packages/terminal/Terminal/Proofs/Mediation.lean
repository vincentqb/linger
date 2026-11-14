module

import all Terminal.CoreCode.Mediation
public import Terminal.CoreSpec
import all Terminal.CoreCode.Vt
import all Terminal.CoreCode.Render
import all Terminal.Proofs.Render

-- Module-private by default: `Vt`'s fields are sealed (see `packages/terminal/Terminal/Proofs/Vt/State.lean`).

/-! # Owned terminal queries without client dependence

The mediator is a pure stream transducer. These theorems pin its exact profile,
its full-result chunk law, its unchanged `Vt.feed` projection, and the bound on
all retained candidate bytes. Presentation-client state does not occur in any
statement or input.
-/

namespace Terminal.Mediation

open Terminal.Vt Terminal.Render

/-! ## Exact normative profile -/

theorem classifyCsi_da1 (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x63] = .owned da1Reply ∧
      classifyCsi v [ESC, 0x5B, 0x30, 0x63] = .owned da1Reply := by
  simp [classifyCsi]

theorem classifyCsi_da2 (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x3E, 0x63] = .owned da2Reply ∧
      classifyCsi v [ESC, 0x5B, 0x3E, 0x30, 0x63] = .owned da2Reply := by
  simp [classifyCsi]

theorem classifyCsi_status (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x35, 0x6E] = .owned (statusReply false) ∧
      classifyCsi v [ESC, 0x5B, 0x3F, 0x35, 0x6E] = .owned (statusReply true) := by
  simp [classifyCsi]

theorem classifyCsi_cpr (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x36, 0x6E] = .owned (cprReply v false) ∧
      classifyCsi v [ESC, 0x5B, 0x3F, 0x36, 0x6E] = .owned (cprReply v true) := by
  simp [classifyCsi]

theorem cprRow_absolute (v : Vt) (h : v.modes.origin = false) : cprRow v = v.cursor.y + 1 := by
  simp [cprRow, Vt.getModes, h]

theorem cprRow_origin_above (v : Vt) (ho : v.modes.origin = true) (hy : v.cursor.y < v.top) :
    cprRow v = 1 := by simp [cprRow, Vt.getModes, stick, ho, hy]

theorem cprRow_origin_inside (v : Vt) (ho : v.modes.origin = true) (hy : ¬v.cursor.y < v.top) :
    cprRow v = v.cursor.y - v.top + 1 := by simp [cprRow, Vt.getModes, stick, ho, hy]

theorem classifyCsi_version (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x3E, 0x71] = .owned versionReply ∧
      classifyCsi v [ESC, 0x5B, 0x3E, 0x30, 0x71] = .owned versionReply := by
  simp [classifyCsi]

theorem classifyCsi_textArea (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x31, 0x38, 0x74] = .owned (textAreaReply v) := by simp [classifyCsi]

theorem classifyCsi_kitty (v : Vt) : classifyCsi v [ESC, 0x5B, 0x3F, 0x75] = .owned [] := by
  simp [classifyCsi]

theorem classifyOsc_fg_bel :
    classifyOsc [ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, BEL] = .owned (paletteReply 0x30 0x66) := by
  simp [classifyOsc]

theorem classifyOsc_fg_st :
    classifyOsc [ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, ESC, STFinal] =
      .owned (paletteReply 0x30 0x66) := by
  simp [classifyOsc]

theorem classifyOsc_bg_bel :
    classifyOsc [ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, BEL] = .owned (paletteReply 0x31 0x30) := by
  simp [classifyOsc]

theorem classifyOsc_bg_st :
    classifyOsc [ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, ESC, STFinal] =
      .owned (paletteReply 0x31 0x30) := by
  simp [classifyOsc]

theorem classifyOsc_cursor_bel :
    classifyOsc [ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, BEL] = .owned (paletteReply 0x32 0x66) := by
  simp [classifyOsc]

theorem classifyOsc_cursor_st :
    classifyOsc [ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, ESC, STFinal] =
      .owned (paletteReply 0x32 0x66) := by
  simp [classifyOsc]

/-- The title reports are owned with no reply: a client's terminal would answer with the title
it shows. -/
theorem classifyCsi_titles (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x32, 0x30, 0x74] = .owned [] ∧
      classifyCsi v [ESC, 0x5B, 0x32, 0x31, 0x74] = .owned [] := by
  simp [classifyCsi]

/-- Any bytes but `;`, then `; ?` and BEL or ST, are what follows `52 ;` in a clipboard query. -/
theorem selectionQuery_query (sel term : Bytes) (h : 0x3B ∉ sel) (ht : terminated term = true) :
    selectionQuery (sel ++ 0x3B :: 0x3F :: term) = true := by
  induction sel with
  | nil => simp [selectionQuery, ht]
  | cons b sel
    ih =>
    have hb : b ≠ 0x3B := by
      intro e
      apply h
      simp [e]
    have hs : 0x3B ∉ sel := by
      intro m
      apply h
      simp [m]
    simp [selectionQuery, hb, ih hs]

/-- **No program reads a client's clipboard through linger.** A clipboard query, whatever its
selection and with either terminator, is owned and gets no reply, so no client receives it. -/
theorem classifyOsc_clipboard (sel term : Bytes) (h : 0x3B ∉ sel)
    (ht : term = [BEL] ∨ term = [ESC, STFinal]) :
    classifyOsc ([ESC, 0x5D, 0x35, 0x32, 0x3B] ++ sel ++ 0x3B :: 0x3F :: term) = .owned [] := by
  have hq : selectionQuery (sel ++ 0x3B :: 0x3F :: term) = true :=
    selectionQuery_query sel term h (by rcases ht with rfl | rfl <;> rfl)
  unfold classifyOsc
  simp [unanswered, unansweredOsc, hq]

/-- The fixed replies themselves have the exact bytes promised by the table. -/
theorem fixed_replies_exact :
    da1Reply = [ESC, 0x5B, 0x3F, 0x31, 0x3B, 0x32, 0x63] ∧
      da2Reply = [ESC, 0x5B, 0x3E, 0x30, 0x3B, 0x30, 0x3B, 0x30, 0x63] ∧
      statusReply false = [ESC, 0x5B, 0x30, 0x6E] ∧
      statusReply true = [ESC, 0x5B, 0x3F, 0x30, 0x6E] ∧
      decrqssReply = [ESC, 0x50, 0x30, 0x24, 0x72, ESC, STFinal] := by
  decide

/-- An owned request is excluded from presentation output and contributes its
single prescribed reply stream. Empty is the table's deliberate zero reply. -/
theorem complete_owned (reply seq : Bytes) :
    complete (.owned reply) seq = { scan := .ground, visible := [], replies := reply } := by rfl

/-- An unowned complete candidate is released byte-for-byte and never gains a
linger reply. -/
theorem complete_unowned (seq : Bytes) :
    complete .unowned seq = { scan := .ground, visible := seq, replies := [] } := by rfl

/-- Completion always returns the scanner to ground, independently of which
exact classifier result was selected. -/
theorem complete_scan (decision : Decision) (seq : Bytes) :
    (complete decision seq).scan = .ground := by cases decision <;> rfl

/-- Any complete CSI outside the owned table is emitted exactly once. -/
theorem step_csi_unowned (v : Vt) (rev : Bytes) (b : UInt8) (he : b ≠ ESC)
    (hf : 0x40 ≤ b ∧ b ≤ 0x7E) (hc : classifyCsi v (b :: rev).reverse = .unowned) :
    (Scan.csi rev).step v b =
      { scan := .ground, visible := (b :: rev).reverse, replies := [] } := by
  have hc' : classifyCsi v (rev.reverse ++ [b]) = .unowned := by simpa using hc
  simp [Scan.step, he, hf, hc', complete]

/-- Any complete OSC outside the owned table is emitted exactly once. -/
theorem step_osc_unowned (v : Vt) (rev : Bytes) (escSeen : Bool) (b : UInt8)
    (hdone : b = BEL ∨ (escSeen = true ∧ b = STFinal))
    (hc : classifyOsc (b :: rev).reverse = .unowned) :
    (Scan.osc rev escSeen).step v b =
      { scan := .ground, visible := (b :: rev).reverse, replies := [] } := by
  have hc' : classifyOsc (rev.reverse ++ [b]) = .unowned := by simpa using hc
  simp [Scan.step, hdone, hc', complete]

/-- XTGETTCAP is negative for every payload and echoes that payload exactly. -/
theorem step_xtgetcap (v : Vt) (payloadRev : Bytes) :
    (Scan.dcs 0x2B payloadRev true).step v STFinal =
      { scan := .ground, visible := [], replies := xtgetcapReply payloadRev.reverse } := by
  simp [Scan.step, complete]

/-- DECRQSS is negative for every selector and emits no selector bytes. -/
theorem step_decrqss (v : Vt) (payloadRev : Bytes) :
    (Scan.dcs 0x24 payloadRev true).step v STFinal =
      { scan := .ground, visible := [], replies := decrqssReply } := by
  simp [Scan.step, complete]

/-! ## No reply linger writes to the child can commit a line

A terminal query's reply is written straight into the child's own input
(`Session.step .ptyOut` routes `replies` to `.writePty`), and the child's
output is untrusted — a `cat` of a hostile file, an ssh stream, a log tail. The
one reply that echoes child bytes, XTGETTCAP, would carry a CR and a shell
command if it echoed them verbatim; on a cooked-mode tty the CR commits a line, so
the untrusted output would run a command. This is the restore stream's bug family
aimed at the child instead of the client: an emitter correct only under an unstated
precondition on what it writes to.

The invariant that closes it: **no reply contains a line terminator** (`0x0D`
CR or `0x0A` LF). Every fixed reply satisfies it by inspection; `cprReply` and
`textAreaReply` carry only digits; and `xtgetcapReply` filters its echo to
the XTGETTCAP alphabet (`capByte`: hex and `;`), none of which is a terminator.
Proved over the whole `feed` stream, so a future reply builder that reintroduced
an echo would fail here rather than ship. -/

/-- A byte stream that cannot terminate a line in the child's input. -/
def NoNl (bs : Bytes) : Prop := ∀ b ∈ bs, b ≠ 0x0D ∧ b ≠ 0x0A

theorem NoNl.nil : NoNl [] := by
  intro b hb; simp at hb

theorem NoNl.append {a b : Bytes} (ha : NoNl a) (hb : NoNl b) : NoNl (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

/-- The filter alphabet is line-terminator-free by construction. -/
theorem capByte_no_nl (b : UInt8) (h : capByte b = true) : b ≠ 0x0D ∧ b ≠ 0x0A :=
  ⟨by
    rintro rfl; revert h; decide, by
    rintro rfl; revert h; decide⟩

/-- Digits are `0x30…0x39`, well above either terminator. -/
theorem noNl_digits (n : Nat) : NoNl (digits n) := fun b hb =>
  let h := (digits_range n b hb).1
  ⟨by
    rintro rfl; exact absurd h (by decide), by
    rintro rfl; exact absurd h (by decide)⟩

/-- A concrete literal reply carries no terminator — the workhorse for the fixed
rows. -/
theorem noNl_lit {bs : Bytes} (h : bs.all (fun b => b != 0x0D && b != 0x0A) = true) : NoNl bs := by
  intro b hb
  have := List.all_eq_true.1 h b hb
  simp only [Bool.and_eq_true, bne_iff_ne] at this
  exact this

/-- The echoed payload survives the filter only within the safe alphabet. -/
theorem noNl_filter (payload : Bytes) : NoNl (payload.filter capByte) := fun b hb =>
  capByte_no_nl b (List.mem_filter.1 hb).2

theorem noNl_xtgetcapReply (payload : Bytes) : NoNl (xtgetcapReply payload) := by
  rw [xtgetcapReply]
  repeat' apply NoNl.append
  · exact noNl_lit (by decide)
  · exact noNl_filter _
  · exact noNl_lit (by decide)

theorem noNl_cprReply (v : Vt) (p : Bool) : NoNl (cprReply v p) := by
  cases p <;> (rw [cprReply]; repeat' apply NoNl.append) <;>
    with_reducible
      first
      | exact noNl_digits _
      | exact noNl_lit (by decide)

theorem noNl_textAreaReply (v : Vt) : NoNl (textAreaReply v) := by
  rw [textAreaReply]
  repeat' apply NoNl.append
  all_goals
    with_reducible
      first
      | exact noNl_digits _
      | exact noNl_lit (by decide)

/-- Every reply `classifyCsi` can name is terminator-free. -/
theorem classifyCsi_reply_noNl (v : Vt) (seq r : Bytes) (h : classifyCsi v seq = .owned r) :
    NoNl r := by
  revert h
  fun_cases classifyCsi v seq
  all_goals
    intro h
    first
    |
      (injection h with e; subst e;
       first
       | exact noNl_lit (by decide)
       | exact noNl_cprReply v _
       | exact noNl_textAreaReply v)
    | exact Decision.noConfusion h

/-- …and every reply `classifyOsc` can name. -/
theorem classifyOsc_reply_noNl (seq r : Bytes) (h : classifyOsc seq = .owned r) : NoNl r := by
  unfold classifyOsc at h
  repeat' split at h
  all_goals
    with_reducible
      first
      | (injection h with e; subst e; exact noNl_lit (by decide))
      | exact Decision.noConfusion h

/-- `complete` produces a terminator-free reply whenever the decision it is given
does. `.unowned` produces no reply at all. -/
theorem complete_reply_noNl {d : Decision} {seq : Bytes} (h : ∀ r, d = .owned r → NoNl r) :
    NoNl (complete d seq).replies := by
  cases d with
  | unowned => exact NoNl.nil
  | owned r => exact h r rfl

/-- One scanner step never emits a line terminator, from any state and any byte.
Replies arise only from `complete`, and every owned reply is one of the
terminator-free builders above (the DCS arm's `xtgetcapReply`/`decrqssReply`
included); `complete .unowned` and every non-completing branch reply is empty. -/
theorem step_reply_noNl (s : Scan) (v : Vt) (b : UInt8) : NoNl (s.step v b).replies := by
  cases s <;> simp only [Scan.step] <;> (repeat' split)
  all_goals
    first
    | exact NoNl.nil
    | exact complete_reply_noNl (fun r hr => classifyCsi_reply_noNl v _ r hr)
    | exact complete_reply_noNl (fun r hr => classifyOsc_reply_noNl _ r hr)
    |
      exact
        complete_reply_noNl
          (fun r hr => by
            injection hr with e; subst e; exact noNl_xtgetcapReply _)
    |
      exact
        complete_reply_noNl
          (fun r hr => by
            injection hr with e; subst e; exact noNl_lit (by decide))

/-- One version for `linger version`, the child's `TERM_PROGRAM_VERSION` and XTVERSION. -/
theorem versionNumber_eq : versionNumber = "0.1.0" := rfl

/-- **linger never writes a line terminator into the child.** The reply stream of
any child output, from any scanner state, contains no CR or LF — so untrusted
output cannot commit a command line through a query reply. It is the child's half of
the mediator's independence from clients, and the guard against reply injection. -/
theorem feed_replies_noNl (v : Vt) (s : Scan) (bs : Bytes) : NoNl (feed v s bs).replies := by
  induction bs generalizing v s with
  | nil =>
    intro b hb; simp [feed] at hb
  | cons c cs ih =>
    simp only [feed]
    exact NoNl.append (step_reply_noNl s (v.step c) c) (ih (v.step c) _)

/-! ## Stream laws -/

/-- The full chunk law: re-chunking preserves the final VT and scanner, concatenates visible
bytes, child replies and marks in order, asks when either part asks, and keeps the later part's
last notification, else the earlier one's. -/
theorem feed_append (v : Vt) (s : Scan) (a b : Bytes) :
    feed v s (a ++ b) =
      let first := feed v s a
      let second := feed first.vt first.scan b
      { vt := second.vt, scan := second.scan, visible := first.visible ++ second.visible,
        replies := first.replies ++ second.replies, asks := first.asks || second.asks,
        notice := second.notice.or first.notice, marks := first.marks ++ second.marks } := by
  induction a generalizing v s with
  | nil => simp [feed, Option.or_none]
  | cons x xs ih =>
    simp only [List.cons_append, feed]
    rw [ih]
    simp only [List.append_assoc, Bool.or_assoc, Option.or_assoc]

/-- The mediator observes every byte but does not alter emulator semantics. -/
theorem feed_vt (v : Vt) (s : Scan) (bytes : Bytes) : (feed v s bytes).vt = v.feed bytes := by
  induction bytes generalizing v s with
  | nil => rfl
  | cons b bs ih =>
    simp only [feed, Vt.feed, List.foldl_cons]
    exact ih (v := v.step b) (s := (s.step (v.step b) b).scan)

/-! ## Exact passthrough for string protocols -/

/-- A body contains no string terminator relative to the scanner's incoming
ESC flag. Query-looking bytes are allowed; only the protocol's `ESC \\` ends
it. -/
def StFree (escSeen : Bool) : Bytes → Prop
  | [] => True
  | b :: bs => (escSeen && b == STFinal) = false ∧ StFree (b == ESC) bs

/-- ESC-flag state after consuming a terminator-free body. -/
def escAfter : Bool → Bytes → Bool
  | escSeen, [] => escSeen
  | _, b :: bs => escAfter (b == ESC) bs

/-- A passthrough string body is emitted byte-for-byte, produces no reply,
and retains only its one-bit ESC flag. -/
theorem feed_strPass_free (v : Vt) (escSeen : Bool) (body : Bytes) (h : StFree escSeen body) :
    let r := feed v (.strPass escSeen) body
    r.scan = .strPass (escAfter escSeen body) ∧ r.visible = body ∧ r.replies = [] := by
  induction body generalizing v escSeen with
  | nil => simp [feed, escAfter]
  | cons b bs ih =>
    simp only [StFree] at h
    obtain ⟨ht, hrest⟩ := h
    have hr := ih (v := v.step b) (escSeen := b == ESC) hrest
    simp [feed, Scan.step, ht, escAfter, hr]

/-- Appending ST to a terminator-free passthrough body emits the complete
string exactly and returns to ground. This remains true when the body ends in
ESC (the explicit terminator contributes a fresh ESC). -/
theorem feed_strPass_st (v : Vt) (escSeen : Bool) (body : Bytes) (h : StFree escSeen body) :
    let r := feed v (.strPass escSeen) (body ++ [ESC, STFinal])
    r.scan = .ground ∧ r.visible = body ++ [ESC, STFinal] ∧ r.replies = [] := by
  have hf := feed_strPass_free v escSeen body h
  rw [feed_append]
  simp only at hf ⊢
  obtain ⟨hs, hv, hr⟩ := hf
  rw [hs, hv, hr]
  simp [feed, Scan.step, ESC, STFinal]

/-- APC/kitty graphics payloads are arbitrary apart from not containing their
own terminator: they pass byte-for-byte and cannot trigger owned CSI queries
inside the payload. -/
theorem apc_passthrough (v : Vt) (payload : Bytes) (h : StFree false payload) :
    let bytes := [ESC, 0x5F] ++ payload ++ [ESC, STFinal]
    let r := feed v .ground bytes
    r.scan = .ground ∧ r.visible = bytes ∧ r.replies = [] := by
  have hp := feed_strPass_st ((v.step ESC).step 0x5F) false payload h
  rw [show [ESC, 0x5F] ++ payload ++ [ESC, STFinal] = [ESC, 0x5F] ++ (payload ++ [ESC, STFinal])
      from rfl]
  dsimp only
  rw [feed_append]
  simp only at hp ⊢
  simp [feed, Scan.step, ESC, STFinal, hp]

/-- Sixel starts with `DCS q`, which is rejected as an owned-DCS candidate on
its first payload byte and then streams in constant memory. -/
theorem sixel_passthrough (v : Vt) (payload : Bytes) (h : StFree false payload) :
    let bytes := [ESC, 0x50, 0x71] ++ payload ++ [ESC, STFinal]
    let r := feed v .ground bytes
    r.scan = .ground ∧ r.visible = bytes ∧ r.replies = [] := by
  have hp := feed_strPass_st (((v.step ESC).step 0x50).step 0x71) false payload h
  rw [show
      [ESC, 0x50, 0x71] ++ payload ++ [ESC, STFinal] =
        [ESC, 0x50, 0x71] ++ (payload ++ [ESC, STFinal])
      from rfl]
  dsimp only
  rw [feed_append]
  simp only at hp ⊢
  simp [feed, Scan.step, ESC, STFinal, hp]

/-! ## Scanner bound -/

/-- One byte preserves the candidate-buffer caps. -/
theorem Scan.Bounded.step {s : Scan} {v : Vt} {b : UInt8} (h : s.Bounded) :
    (s.step v b).scan.Bounded := by
  cases s <;> unfold Scan.step <;> dsimp only
  all_goals repeat' split
  all_goals
    simp_all [Scan.Bounded, Scan.pending, complete_scan, Nat.succ_le_iff, csiCap, oscCap, dcsCap]

/-- Every finite child-output stream preserves the candidate-buffer caps. -/
theorem feed_bounded (v : Vt) (s : Scan) (bytes : Bytes) (h : s.Bounded) :
    (feed v s bytes).scan.Bounded := by
  induction bytes generalizing v s with
  | nil => simpa [feed] using h
  | cons b bs ih =>
    simp only [feed]
    exact ih (v := v.step b) (s := (s.step (v.step b) b).scan) h.step

/-- `finish` emits exactly the pending bytes and always resets to a bounded
scanner. It cannot emit a child reply because its type has no reply field. -/
theorem finish_exact (s : Scan) : finish s = (s.pending, .ground) := by rfl

theorem finish_bounded (s : Scan) : (finish s).2.Bounded := by simp [finish, Scan.Bounded]

/-! ### The caps, as a bound on emitted bytes

`Scan.Bounded` names all three caps, and `feed_bounded` preserves it — but `Bounded` is a
`def` over the *stored* field, so nothing so far states what the caps buy a **client**.
`Scan.pending` is the run `finish` flushes into the broadcast, so these turn the invariant
into a bound on bytes that actually leave the daemon. -/

/-- **The caps bound the retained run**, from any bounded scanner. -/
theorem Scan.pending_le_caps {s : Scan} (h : s.Bounded) :
    s.pending.length ≤ max csiCap (max oscCap dcsCap) := by
  cases s <;> simp_all [Scan.Bounded, Scan.pending, csiCap, oscCap, dcsCap] <;> omega

/-- **…for every finite child-output stream.** However many megabytes of hostile output the
child writes, the scanner is holding at most one cap's worth when the stream stops. -/
theorem feed_pending_le_caps (v : Vt) (s : Scan) (bs : Bytes) (h : s.Bounded) :
    (feed v s bs).scan.pending.length ≤ max csiCap (max oscCap dcsCap) :=
  Scan.pending_le_caps (feed_bounded v s bs h)

/-- **…and the flush the daemon broadcasts on child exit is bounded by the same.** This is
the one a client can observe, which is why the chain ends here rather than at `Bounded`. -/
theorem finish_pending_le_caps (s : Scan) (h : s.Bounded) :
    (finish s).1.length ≤ max csiCap (max oscCap dcsCap) := by
  rw [finish_exact]
  exact Scan.pending_le_caps h

/-! ## A program that asks for someone

What `Scan.hears` hears, byte by byte: a BEL rings where a terminal executes it, and nowhere
else, and an OSC string asks exactly when it posts a notification. Over a whole stream: plain
output asks nothing, a bell asks, and an OSC within the cap, ended by BEL or ST, asks exactly
when its payload posts a notification, with that notification's text, whatever the chunks. A
notification's text is never longer than the OSC buffer's cap. -/

/-- A BEL in ground rings: it asks, with no notification. -/
theorem hears_bell : Scan.ground.hears BEL = { asks := true } := rfl

/-- …as it does after ESC and within a control sequence, where a terminal executes a control. -/
theorem hears_bell_sequence (rev : Bytes) :
    Scan.esc.hears BEL = { asks := true } ∧
      (Scan.csi rev).hears BEL = { asks := true } ∧ Scan.csiPass.hears BEL = { asks := true } :=
  ⟨rfl, rfl, rfl⟩

/-- Outside a string, every other byte asks nothing. -/
theorem hears_outside (b : UInt8) (h : b ≠ BEL) (rev : Bytes) :
    Scan.ground.hears b = {} ∧
      Scan.esc.hears b = {} ∧ (Scan.csi rev).hears b = {} ∧ Scan.csiPass.hears b = {} := by
  simp [Scan.hears, h]

/-- A byte within a DCS, SOS, PM or APC string, or within an OSC string past its cap, asks
nothing, a BEL included: it is the string's. -/
theorem hears_string (escSeen : Bool) (kind : UInt8) (payloadRev : Bytes) (b : UInt8) :
    (Scan.strPass escSeen).hears b = {} ∧
      Scan.dcsIntro.hears b = {} ∧
      (Scan.dcsKind kind).hears b = {} ∧
      (Scan.dcs kind payloadRev escSeen).hears b = {} ∧ (Scan.oscPass escSeen).hears b = {} :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The BEL that ends an OSC string rings no bell: the string asks only when it posts a
notification. -/
theorem hears_osc_end (rev : Bytes) (escSeen : Bool) :
    (Scan.osc rev escSeen).hears BEL = heardOsc (heldPayload rev) := by simp [Scan.hears]

/-- What an OSC payload tells is a notification exactly when it posts one. -/
theorem heardOsc_eq (payload : Bytes) :
    heardOsc payload = { asks := (noticeOf payload).isSome, notice := noticeOf payload } := by
  unfold heardOsc
  split <;> simp_all

/-- An OSC 9 payload posts its text, unless that is a ConEmu sub-command. -/
theorem noticeOf_osc9 (text : Bytes) :
    noticeOf (0x39 :: 0x3B :: text) = if subcommand text then none else some text := rfl

/-- ConEmu's progress report, `9;4;…`, posts nothing. -/
theorem noticeOf_progress (rest : Bytes) :
    noticeOf (0x39 :: 0x3B :: 0x34 :: 0x3B :: rest) = none := by simp [noticeOf, subcommand, digit]

/-- A byte is heard as a notification only where the scanner lets go of an OSC: as BEL or ST
completes it, or as the scanner releases one past its cap unclassified. -/
theorem hears_notice_releases (s : Scan) (v : Vt) (b : UInt8) (h : (s.hears b).notice.isSome) :
    ∃ rev escSeen,
      s = .osc rev escSeen ∧
        ((s.step v b).scan = .ground ∨ (s.step v b).scan = .oscPass (b == ESC)) := by
  cases s with
  | osc rev escSeen =>
    refine ⟨rev, escSeen, rfl, ?_⟩
    simp only [Scan.hears] at h
    simp only [Scan.step]
    split
    · exact .inl (complete_scan _ _)
    · rename_i hend
      simp only [hend] at h
      split
      · rename_i hfit
        simp [hfit] at h
      · exact .inr rfl
  | _ => simp [Scan.hears] at h

/-- Feeding a byte, then the rest, asks when the byte or the rest asks, and posts the rest's last
notification, else the byte's. -/
theorem hears_feed_cons (v : Vt) (s : Scan) (b : UInt8) (bs : Bytes) :
    (feed v s (b :: bs)).asks =
        ((s.hears b).asks || (feed (v.step b) (s.step (v.step b) b).scan bs).asks) ∧
      (feed v s (b :: bs)).notice =
        (feed (v.step b) (s.step (v.step b) b).scan bs).notice.or (s.hears b).notice := ⟨rfl, rfl⟩

/-- One byte asks as `Scan.hears` hears it, and posts what it hears. -/
theorem feed_single (v : Vt) (s : Scan) (b : UInt8) :
    (feed v s [b]).asks = (s.hears b).asks ∧
      (feed v s [b]).notice = (s.hears b).notice ∧
      (feed v s [b]).scan = (s.step (v.step b) b).scan := by
  simp [feed]

/-- `feed_append`, read through what the chunk tells of asking and where it leaves the
scanner. -/
theorem feed_append_heard (v : Vt) (s : Scan) (a b : Bytes) :
    (feed v s (a ++ b)).asks =
        ((feed v s a).asks || (feed (feed v s a).vt (feed v s a).scan b).asks) ∧
      (feed v s (a ++ b)).notice =
        (feed (feed v s a).vt (feed v s a).scan b).notice.or (feed v s a).notice ∧
      (feed v s (a ++ b)).scan = (feed (feed v s a).vt (feed v s a).scan b).scan := by
  rw [feed_append]
  exact ⟨rfl, rfl, rfl⟩

/-- **Plain output asks nothing**: bytes with no BEL and no ESC, fed from ground, ring no bell
and post no notification. -/
theorem feed_plain_quiet (v : Vt) (bs : Bytes) (h : ∀ b ∈ bs, b ≠ BEL ∧ b ≠ ESC) :
    (feed v .ground bs).asks = false ∧ (feed v .ground bs).notice = none := by
  induction bs generalizing v with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    obtain ⟨hbel, hesc⟩ := h b List.mem_cons_self
    have hstep : (Scan.ground.step (v.step b) b).scan = .ground := by simp [Scan.step, hesc]
    have hrest := ih (v.step b) fun c hc => h c (List.mem_cons_of_mem b hc)
    rw [(hears_feed_cons v .ground b bs).1, (hears_feed_cons v .ground b bs).2, hstep,
      (hears_outside b hbel []).1]
    simp [hrest.1, hrest.2]

/-- **A bell asks**: a chunk that holds a BEL in ground asks, wherever it is in the chunk. -/
theorem feed_bell (v : Vt) (before after : Bytes) (h : ∀ b ∈ before, b ≠ ESC) :
    (feed v .ground (before ++ BEL :: after)).asks = true := by
  induction before generalizing v with
  | nil => simp [feed, Scan.hears]
  | cons b bs ih =>
    have hesc := h b List.mem_cons_self
    have hstep : (Scan.ground.step (v.step b) b).scan = .ground := by simp [Scan.step, hesc]
    rw [List.cons_append, (hears_feed_cons v .ground b _).1, hstep,
      ih (v.step b) fun c hc => h c (List.mem_cons_of_mem b hc), Bool.or_true]

/-- Payload bytes an OSC holds as it reads them: none ends the string or begins its
terminator. -/
def Plain (payload : Bytes) : Prop := ∀ b ∈ payload, b ≠ BEL ∧ b ≠ ESC

/-- An OSC within its cap reads plain payload bytes into its buffer, and hears nothing yet. -/
theorem feed_osc_plain (v : Vt) (rev payload : Bytes) (h : Plain payload)
    (fits : rev.length + payload.length ≤ oscCap) :
    (feed v (.osc rev false) payload).scan = .osc (payload.reverse ++ rev) false ∧
      (feed v (.osc rev false) payload).asks = false ∧
      (feed v (.osc rev false) payload).notice = none := by
  induction payload generalizing v rev with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons b bs ih =>
    obtain ⟨hbel, hesc⟩ := h b List.mem_cons_self
    simp only [List.length_cons] at fits
    have hfit : rev.length < oscCap := by omega
    have hstep : ((Scan.osc rev false).step (v.step b) b).scan = .osc (b :: rev) false := by
      simp [Scan.step, hbel, hfit, hesc]
    have hheard : (Scan.osc rev false).hears b = {} := by simp [Scan.hears, hbel, hfit]
    have hrest :=
      ih (v.step b) (b :: rev) (fun c hc => h c (List.mem_cons_of_mem b hc))
        (by
          simp only [List.length_cons]; omega)
    have hscan :
      (feed v (.osc rev false) (b :: bs)).scan =
        (feed (v.step b) ((Scan.osc rev false).step (v.step b) b).scan bs).scan :=
      rfl
    rw [hscan, (hears_feed_cons v _ b bs).1, (hears_feed_cons v _ b bs).2, hstep, hheard]
    simp [hrest.1, hrest.2.1, hrest.2.2]

/-- The payload of an OSC buffer that holds `ESC ]` and plain payload bytes is those bytes, with
or without the ESC that begins ST after them. -/
theorem heldPayload_plain (payload : Bytes) (h : Plain payload) :
    heldPayload (payload.reverse ++ [0x5D, ESC]) = payload ∧
      heldPayload (ESC :: (payload.reverse ++ [0x5D, ESC])) = payload := by
  have hopen : heldPayload (payload.reverse ++ [0x5D, ESC]) = payload := by
    unfold heldPayload
    cases hp : payload.reverse with
    | nil =>
      have : payload = [] := List.reverse_eq_nil_iff.mp hp
      subst this
      rfl
    | cons last
      front =>
      have hlast : last ≠ ESC := by
        have hm : last ∈ payload := by
          rw [← List.mem_reverse, hp]
          exact List.mem_cons_self
        exact (h last hm).2
      rw [List.cons_append, List.dropWhile_cons_of_neg (by simpa using hlast), ← List.cons_append, ←
        hp, List.reverse_append, List.reverse_reverse]
      rfl
  refine ⟨hopen, ?_⟩
  have hesc : ∀ held : Bytes, heldPayload (ESC :: held) = heldPayload held := by
    intro held
    simp [heldPayload]
  exact (hesc _).trans hopen

/-- `ESC ]` from ground opens an OSC and hears nothing. -/
theorem feed_osc_open (v : Vt) :
    (feed v .ground [ESC, 0x5D]).scan = .osc [0x5D, ESC] false ∧
      (feed v .ground [ESC, 0x5D]).asks = false ∧ (feed v .ground [ESC, 0x5D]).notice = none := by
  simp [feed, Scan.step, Scan.hears, ESC, BEL]

/-- **A notification is heard as its string ends**: an OSC with a plain payload, within its cap
and ended by BEL or by ST, asks exactly when the payload posts a notification, with that
notification's text. ST needs one byte of the buffer more, for its ESC. -/
theorem feed_osc_notice (v : Vt) (payload : Bytes) (h : Plain payload)
    (fits : payload.length + 3 ≤ oscCap) (ending : Bytes)
    (ends : ending = [BEL] ∨ ending = [ESC, STFinal]) :
    (feed v .ground ([ESC, 0x5D] ++ payload ++ ending)).asks = (noticeOf payload).isSome ∧
      (feed v .ground ([ESC, 0x5D] ++ payload ++ ending)).notice = noticeOf payload := by
  obtain ⟨o1, o2, o3⟩ := feed_osc_open v
  obtain ⟨a1, a2, -⟩ := feed_append_heard v .ground [ESC, 0x5D] (payload ++ ending)
  obtain ⟨b1, b2, -⟩ :=
    feed_append_heard (feed v .ground [ESC, 0x5D]).vt (feed v .ground [ESC, 0x5D]).scan payload
      ending
  rw [List.append_assoc, a1, a2, b1, b2, o1, o2, o3]
  generalize (feed v .ground [ESC, 0x5D]).vt = w
  obtain ⟨p1, p2, p3⟩ :=
    feed_osc_plain w [0x5D, ESC] payload h
      (by
        simp only [List.length_cons, List.length_nil]; omega)
  rw [p1, p2, p3]
  generalize (feed w (.osc [0x5D, ESC] false) payload).vt = u
  have hfit : payload.length + 2 < oscCap := by omega
  rcases ends with rfl | rfl
  · obtain ⟨e1, e2, -⟩ := feed_single u (.osc (payload.reverse ++ [0x5D, ESC]) false) BEL
    rw [e1, e2, hears_osc_end, (heldPayload_plain payload h).1, heardOsc_eq]
    simp
  · have hne : ESC ≠ BEL := by decide
    have hesc : (Scan.osc (payload.reverse ++ [0x5D, ESC]) false).hears ESC = {} := by
      simp [Scan.hears, hfit, hne]
    have hstep :
      ((Scan.osc (payload.reverse ++ [0x5D, ESC]) false).step (u.step ESC) ESC).scan =
        .osc (ESC :: (payload.reverse ++ [0x5D, ESC])) true := by
      simp [Scan.step, hfit, hne]
    have hst :
      (Scan.osc (ESC :: (payload.reverse ++ [0x5D, ESC])) true).hears STFinal =
        heardOsc payload := by
      simp [Scan.hears, (heldPayload_plain payload h).2]
    obtain ⟨c1, c2⟩ := hears_feed_cons u (.osc (payload.reverse ++ [0x5D, ESC]) false) ESC [STFinal]
    rw [c1, c2, hstep, hesc]
    obtain ⟨e1, e2, -⟩ :=
      feed_single (u.step ESC) (.osc (ESC :: (payload.reverse ++ [0x5D, ESC])) true) STFinal
    rw [e1, e2, hst, heardOsc_eq]
    simp

/-- A notification's text is no longer than the payload it comes from. -/
theorem noticeOf_length (payload text : Bytes) (h : noticeOf payload = some text) :
    text.length ≤ payload.length := by
  unfold noticeOf at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [List.length_cons]
      omega
  · simp only [Option.some.injEq] at h
    subst h
    rename_i rest
    have whole :=
      congrArg List.length
        (List.takeWhile_append_dropWhile (p := (· != (0x3B : UInt8))) (l := rest))
    simp only [List.length_append] at whole
    simp only [List.length_cons]
    split
    · simp only [List.length_drop]
      omega
    · split
      · omega
      · simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop]
        omega
  · simp at h

/-- The payload of an OSC buffer is shorter than the buffer by the `ESC ]` it opens with. -/
theorem heldPayload_length (rev : Bytes) : (heldPayload rev).length ≤ rev.length - 2 := by
  unfold heldPayload
  simp only [List.length_drop, List.length_reverse]
  have := (List.dropWhile_suffix (l := rev) (p := (· == ESC))).length_le
  omega

/-- **A notification's text fits the OSC buffer's cap**: from a scanner within its caps, what
any byte posts is at most `oscCap` bytes. -/
theorem hears_notice_le {s : Scan} (hs : s.Bounded) (b : UInt8) (text : Bytes)
    (h : (s.hears b).notice = some text) : text.length ≤ oscCap := by
  cases s with
  | osc rev escSeen =>
    simp only [Scan.Bounded] at hs
    simp only [Scan.hears] at h
    split at h
    · rw [heardOsc_eq] at h
      have := noticeOf_length _ _ h
      have := heldPayload_length rev
      omega
    · split at h
      · simp at h
      · rw [heardOsc_eq] at h
        have := noticeOf_length _ _ h
        have := heldPayload_length (b :: rev)
        simp only [List.length_cons] at this
        omega
  | _ => simp [Scan.hears] at h

/-- …over any stream from a scanner within its caps. -/
theorem feed_notice_le (v : Vt) (s : Scan) (bs : Bytes) (hs : s.Bounded) (text : Bytes)
    (h : (feed v s bs).notice = some text) : text.length ≤ oscCap := by
  induction bs generalizing v s with
  | nil => simp [feed] at h
  | cons b bs ih =>
    rw [(hears_feed_cons v s b bs).2] at h
    cases hrest : (feed (v.step b) (s.step (v.step b) b).scan bs).notice with
    | some t =>
      rw [hrest, Option.some_or] at h
      cases h
      exact ih (v.step b) _ hs.step hrest
    | none =>
      rw [hrest, Option.none_or] at h
      exact hears_notice_le hs b text h

/-! ## A shell's marks

What `Scan.mark` hears, byte by byte: a mark only where the scanner lets go of an OSC, as BEL or
ST completes it or as the scanner releases one past its cap. Over a whole stream: an OSC within
the cap, with a plain payload and ended by BEL or ST, completes exactly the mark its payload is,
whatever the chunks; and the command line a mark gives is never longer than the OSC buffer's
cap. -/

/-- Feeding a byte, then the rest, completes the byte's mark, then the rest's. -/
theorem marks_feed_cons (v : Vt) (s : Scan) (b : UInt8) (bs : Bytes) :
    (feed v s (b :: bs)).marks =
      (s.mark b).toList ++ (feed (v.step b) (s.step (v.step b) b).scan bs).marks := rfl

/-- `feed_append`, read through the marks. -/
theorem feed_append_marks (v : Vt) (s : Scan) (a b : Bytes) :
    (feed v s (a ++ b)).marks =
      (feed v s a).marks ++ (feed (feed v s a).vt (feed v s a).scan b).marks := by
  rw [feed_append]

/-- One byte completes the mark `Scan.mark` hears. -/
theorem feed_single_mark (v : Vt) (s : Scan) (b : UInt8) :
    (feed v s [b]).marks = (s.mark b).toList := by simp [feed]

/-- A byte completes a mark only where the scanner lets go of an OSC: as BEL or ST completes it,
or as the scanner releases one past its cap unclassified. -/
theorem mark_releases (s : Scan) (v : Vt) (b : UInt8) (h : (s.mark b).isSome) :
    ∃ rev escSeen,
      s = .osc rev escSeen ∧
        ((s.step v b).scan = .ground ∨ (s.step v b).scan = .oscPass (b == ESC)) := by
  cases s with
  | osc rev escSeen =>
    refine ⟨rev, escSeen, rfl, ?_⟩
    simp only [Scan.mark] at h
    simp only [Scan.step]
    split
    · exact .inl (complete_scan _ _)
    · rename_i hend
      simp only [hend] at h
      split
      · rename_i hfit
        simp [hfit] at h
      · exact .inr rfl
  | _ => simp [Scan.mark] at h

/-- `ESC ]` from ground opens an OSC and completes no mark. -/
theorem feed_osc_open_marks (v : Vt) : (feed v .ground [ESC, 0x5D]).marks = [] := by
  simp [feed, Scan.step, Scan.mark, ESC]

/-- An OSC within its cap reads plain payload bytes and completes no mark yet. -/
theorem feed_osc_plain_marks (v : Vt) (rev payload : Bytes) (h : Plain payload)
    (fits : rev.length + payload.length ≤ oscCap) :
    (feed v (.osc rev false) payload).marks = [] := by
  induction payload generalizing v rev with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨hbel, hesc⟩ := h b List.mem_cons_self
    simp only [List.length_cons] at fits
    have hfit : rev.length < oscCap := by omega
    have hstep : ((Scan.osc rev false).step (v.step b) b).scan = .osc (b :: rev) false := by
      simp [Scan.step, hbel, hfit, hesc]
    have hmark : (Scan.osc rev false).mark b = none := by simp [Scan.mark, hbel, hfit]
    rw [marks_feed_cons, hstep, hmark,
      ih (v.step b) (b :: rev) (fun c hc => h c (List.mem_cons_of_mem b hc))
        (by
          simp only [List.length_cons]; omega)]
    rfl

/-- **A mark is heard as its string ends**: an OSC with a plain payload, within its cap and ended
by BEL or by ST, completes exactly the mark its payload is, read as a whole payload. ST needs one
byte of the buffer more, for its ESC. -/
theorem feed_osc_mark (v : Vt) (payload : Bytes) (h : Plain payload)
    (fits : payload.length + 3 ≤ oscCap) (ending : Bytes)
    (ends : ending = [BEL] ∨ ending = [ESC, STFinal]) :
    (feed v .ground ([ESC, 0x5D] ++ payload ++ ending)).marks = (markOf payload true).toList := by
  rw [List.append_assoc, feed_append_marks, feed_osc_open_marks, List.nil_append,
    (feed_osc_open v).1]
  generalize (feed v .ground [ESC, 0x5D]).vt = w
  rw [feed_append_marks,
    feed_osc_plain_marks w [0x5D, ESC] payload h
      (by
        simp only [List.length_cons, List.length_nil]; omega),
    List.nil_append,
    (feed_osc_plain w [0x5D, ESC] payload h
        (by
          simp only [List.length_cons, List.length_nil]; omega)).1]
  generalize (feed w (.osc [0x5D, ESC] false) payload).vt = u
  have hfit : payload.length + 2 < oscCap := by omega
  rcases ends with rfl | rfl
  · rw [feed_single_mark]
    simp [Scan.mark, (heldPayload_plain payload h).1]
  · have hne : ESC ≠ BEL := by decide
    have hesc : (Scan.osc (payload.reverse ++ [0x5D, ESC]) false).mark ESC = none := by
      simp [Scan.mark, hfit, hne]
    have hstep :
      ((Scan.osc (payload.reverse ++ [0x5D, ESC]) false).step (u.step ESC) ESC).scan =
        .osc (ESC :: (payload.reverse ++ [0x5D, ESC])) true := by
      simp [Scan.step, hfit, hne]
    rw [marks_feed_cons, hesc, hstep, feed_single_mark]
    simp [Scan.mark, (heldPayload_plain payload h).2]

/-- A %-decoded value is no longer than the bytes it is read from. -/
theorem urlValue_length (bs : Bytes) : (urlValue bs).1.length ≤ bs.length := by
  fun_induction urlValue bs <;> simp_all
  omega

/-- …nor is a `printf %q` word. -/
theorem wordValue_length (q : Quoting) (bs : Bytes) : (wordValue q bs).1.length ≤ bs.length := by
  fun_induction wordValue q bs <;> simp_all <;> omega

/-- A command line is no longer than the parameters it is read from. -/
theorem cmdlineOf_length (whole : Bool) (params : Bytes) :
    (cmdlineOf whole params).bytes.length ≤ params.length := by
  fun_induction cmdlineOf whole params
  · simp
  · exact
      Nat.le_trans (urlValue_length _)
        (by
          simp only [List.length_drop, List.length_cons]; omega)
  · exact
      Nat.le_trans (wordValue_length .bare _)
        (by
          simp only [List.length_drop, List.length_cons]; omega)
  all_goals
    simp only [List.length_cons]
    omega

/-- The command line a mark gives is no longer than its payload. -/
theorem markOf_cmdline_le (payload : Bytes) (whole : Bool) (cmdline : Cmdline)
    (h : markOf payload whole = some (.runs cmdline)) : cmdline.bytes.length ≤ payload.length := by
  unfold markOf at h
  split at h
  · rename_i letter params
    repeat' split at h
    all_goals simp only [Option.some.injEq, reduceCtorEq, Mark.runs.injEq] at h
    subst h
    have := cmdlineOf_length whole params
    simp only [List.length_cons]
    omega
  · simp at h

/-- **A command line fits the OSC buffer's cap**: from a scanner within its caps, the command
line any byte's mark gives is at most `oscCap` bytes. -/
theorem mark_cmdline_le {s : Scan} (hs : s.Bounded) (b : UInt8) (cmdline : Cmdline)
    (h : s.mark b = some (.runs cmdline)) : cmdline.bytes.length ≤ oscCap := by
  cases s with
  | osc rev escSeen =>
    simp only [Scan.Bounded] at hs
    simp only [Scan.mark] at h
    split at h
    · have := markOf_cmdline_le _ _ _ h
      have := heldPayload_length rev
      omega
    · split at h
      · simp at h
      · have := markOf_cmdline_le _ _ _ h
        have := heldPayload_length (b :: rev)
        simp only [List.length_cons] at this
        omega
  | _ => simp [Scan.mark] at h

/-- …over any stream from a scanner within its caps. -/
theorem feed_cmdline_le (v : Vt) (s : Scan) (bs : Bytes) (hs : s.Bounded) (cmdline : Cmdline)
    (h : .runs cmdline ∈ (feed v s bs).marks) : cmdline.bytes.length ≤ oscCap := by
  induction bs generalizing v s with
  | nil => simp [feed] at h
  | cons b bs ih =>
    rw [marks_feed_cons, List.mem_append] at h
    rcases h with h | h
    · exact mark_cmdline_le hs b cmdline (Option.mem_toList.mp h)
    · exact ih (v.step b) _ hs.step h

end Terminal.Mediation
