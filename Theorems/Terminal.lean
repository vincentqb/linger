module

public import Linger.Core.Terminal
public import Theorems.Render
import all Linger.Core.Terminal
import all Linger.Core.Vt
import all Linger.Core.Render
import all Theorems.Render

public section

/-! # §Terminal — owned terminal queries without client dependence

The mediator is a pure stream transducer. These theorems pin its exact profile,
its full-result chunk law, its unchanged `Vt.feed` projection, and the bound on
all retained candidate bytes. Presentation-client state does not occur in any
statement or input.
-/

namespace Linger.Core.Terminal

open Linger.Core.Vt Linger.Core.Render

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
  simp [cprRow, h]

theorem cprRow_origin_above (v : Vt) (ho : v.modes.origin = true) (hy : v.cursor.y < v.top) :
    cprRow v = 1 := by simp [cprRow, ho, hy]

theorem cprRow_origin_inside (v : Vt) (ho : v.modes.origin = true) (hy : ¬v.cursor.y < v.top) :
    cprRow v = v.cursor.y - v.top + 1 := by simp [cprRow, ho, hy]

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

/-- The fixed replies themselves have the exact bytes promised by the table. -/
theorem fixed_replies_exact :
    da1Reply = [ESC, 0x5B, 0x3F, 0x31, 0x3B, 0x32, 0x63] ∧
      da2Reply = [ESC, 0x5B, 0x3E, 0x30, 0x3B, 0x30, 0x3B, 0x30, 0x63] ∧
      statusReply false = [ESC, 0x5B, 0x30, 0x6E] ∧
      statusReply true = [ESC, 0x5B, 0x3F, 0x30, 0x6E] ∧
      decrqssReply = [ESC, 0x50, 0x30, 0x24, 0x72, ESC, STFinal] := by
  decide

/-- Dynamic replies expose only the sampled state named by the contract. -/
theorem cprReply_exact (v : Vt) (private_ : Bool) :
    cprReply v private_ =
      [ESC, 0x5B] ++ (if private_ then [0x3F] else []) ++ digits (cprRow v) ++ [0x3B] ++
        digits (v.cursor.x + 1) ++
        [0x52] := by
  rfl

theorem textAreaReply_exact (v : Vt) :
    textAreaReply v =
      [ESC, 0x5B, 0x38, 0x3B] ++ digits v.rows ++ [0x3B] ++ digits v.cols ++ [0x74] := by
  rfl

theorem xtgetcapReply_exact (payload : Bytes) :
    xtgetcapReply payload =
      [ESC, 0x50, 0x30, 0x2B, 0x72] ++ payload.filter capByte ++ [ESC, STFinal] := by
  rfl

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
(`Session.onMsg .ptyOut` routes `replies` to `.writePty`), and the child's
output is untrusted — a `cat` of a hostile file, an ssh stream, a log tail. The
one reply that echoed child bytes, XTGETTCAP, could carry a CR and a shell
command; on a cooked-mode tty the CR commits a line, so the untrusted output ran
a command. This is the §Replay bug family aimed at the child instead of the
client: an emitter correct only under an unstated precondition on what it writes
to.

The invariant that closes it: **no reply contains a line terminator** (`0x0D`
CR or `0x0A` LF). Every fixed reply satisfies it by inspection; `cprReply` and
`textAreaReply` carry only digits; and `xtgetcapReply` now filters its echo to
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
    first
    | exact noNl_digits _
    | exact noNl_lit (by decide)

theorem noNl_textAreaReply (v : Vt) : NoNl (textAreaReply v) := by
  rw [textAreaReply]
  repeat' apply NoNl.append
  all_goals
    first
    | exact noNl_digits _
    | exact noNl_lit (by decide)

/-- Every reply `classifyCsi` can name is terminator-free. -/
theorem classifyCsi_reply_noNl (v : Vt) (seq r : Bytes) (h : classifyCsi v seq = .owned r) :
    NoNl r := by
  unfold classifyCsi at h
  repeat' split at h
  all_goals
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

/-- **linger never writes a line terminator into the child.** The reply stream of
any child output, from any scanner state, contains no CR or LF — so untrusted
output cannot commit a command line through a query reply. Anchor: the child half
of §Terminal's client-independence, and the injection guard the audit added. -/
theorem feed_replies_noNl (v : Vt) (s : Scan) (bs : Bytes) : NoNl (feed v s bs).replies := by
  induction bs generalizing v s with
  | nil =>
    intro b hb; simp [feed] at hb
  | cons c cs ih =>
    simp only [feed]
    exact NoNl.append (step_reply_noNl s (v.step c) c) (ih (v.step c) _)

/-! ## Stream laws -/

/-- Full §Chunk law: re-chunking preserves the final VT and scanner, and
concatenates visible bytes and child replies in order. -/
theorem feed_append (v : Vt) (s : Scan) (a b : Bytes) :
    feed v s (a ++ b) =
      let first := feed v s a
      let second := feed first.vt first.scan b
      { vt := second.vt, scan := second.scan, visible := first.visible ++ second.visible,
        replies := first.replies ++ second.replies } := by
  induction a generalizing v s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, feed]
    rw [ih]
    simp only [List.append_assoc]

/-- Projection forms of the full law, used by protocol-specific proofs. -/
theorem feed_append_visible (v : Vt) (s : Scan) (a b : Bytes) :
    (feed v s (a ++ b)).visible =
      (feed v s a).visible ++ (feed (feed v s a).vt (feed v s a).scan b).visible := by
  rw [feed_append]

theorem feed_append_replies (v : Vt) (s : Scan) (a b : Bytes) :
    (feed v s (a ++ b)).replies =
      (feed v s a).replies ++ (feed (feed v s a).vt (feed v s a).scan b).replies := by
  rw [feed_append]

theorem feed_append_scan (v : Vt) (s : Scan) (a b : Bytes) :
    (feed v s (a ++ b)).scan = (feed (feed v s a).vt (feed v s a).scan b).scan := by
  rw [feed_append]

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
  all_goals omega

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

end Linger.Core.Terminal
