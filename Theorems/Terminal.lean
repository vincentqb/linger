import Zmx.Core.Terminal
/-! # §Terminal — owned terminal queries without client dependence

The mediator is a pure stream transducer. These theorems pin its exact profile,
its full-result chunk law, its unchanged `Vt.feed` projection, and the bound on
all retained candidate bytes. Presentation-client state does not occur in any
statement or input.
-/

namespace Zmx.Core.Terminal

open Zmx.Core.Vt Zmx.Core.Render

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

theorem cprRow_absolute (v : Vt) (h : v.modes.origin = false) :
    cprRow v = v.cursor.y + 1 := by
  simp [cprRow, h]

theorem cprRow_origin_above (v : Vt) (ho : v.modes.origin = true)
    (hy : v.cursor.y < v.top) : cprRow v = 1 := by
  simp [cprRow, ho, hy]

theorem cprRow_origin_inside (v : Vt) (ho : v.modes.origin = true)
    (hy : ¬v.cursor.y < v.top) : cprRow v = v.cursor.y - v.top + 1 := by
  simp [cprRow, ho, hy]

theorem classifyCsi_version (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x3E, 0x71] = .owned versionReply ∧
    classifyCsi v [ESC, 0x5B, 0x3E, 0x30, 0x71] = .owned versionReply := by
  simp [classifyCsi]

theorem classifyCsi_textArea (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x31, 0x38, 0x74] = .owned (textAreaReply v) := by
  simp [classifyCsi]

theorem classifyCsi_kitty (v : Vt) :
    classifyCsi v [ESC, 0x5B, 0x3F, 0x75] = .owned [] := by
  simp [classifyCsi]

theorem classifyOsc_fg_bel :
    classifyOsc [ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, BEL] =
      .owned (paletteReply 0x30 0x66) := by
  simp [classifyOsc]

theorem classifyOsc_fg_st :
    classifyOsc [ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, ESC, STFinal] =
      .owned (paletteReply 0x30 0x66) := by
  simp [classifyOsc]

theorem classifyOsc_bg_bel :
    classifyOsc [ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, BEL] =
      .owned (paletteReply 0x31 0x30) := by
  simp [classifyOsc]

theorem classifyOsc_bg_st :
    classifyOsc [ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, ESC, STFinal] =
      .owned (paletteReply 0x31 0x30) := by
  simp [classifyOsc]

theorem classifyOsc_cursor_bel :
    classifyOsc [ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, BEL] =
      .owned (paletteReply 0x32 0x66) := by
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
      [ESC, 0x5B] ++ (if private_ then [0x3F] else []) ++
        digits (cprRow v) ++ [0x3B] ++ digits (v.cursor.x + 1) ++ [0x52] := rfl

theorem textAreaReply_exact (v : Vt) :
    textAreaReply v = [ESC, 0x5B, 0x38, 0x3B] ++ digits v.rows ++
      [0x3B] ++ digits v.cols ++ [0x74] := rfl

theorem xtgetcapReply_exact (payload : Bytes) :
    xtgetcapReply payload =
      [ESC, 0x50, 0x30, 0x2B, 0x72] ++ payload ++ [ESC, STFinal] := rfl

/-- An owned request is excluded from presentation output and contributes its
single prescribed reply stream. Empty is the table's deliberate zero reply. -/
theorem complete_owned (reply seq : Bytes) :
    complete (.owned reply) seq =
      { scan := .ground, visible := [], replies := reply } := rfl

/-- An unowned complete candidate is released byte-for-byte and never gains a
linger reply. -/
theorem complete_unowned (seq : Bytes) :
    complete .unowned seq =
      { scan := .ground, visible := seq, replies := [] } := rfl

/-- Completion always returns the scanner to ground, independently of which
exact classifier result was selected. -/
theorem complete_scan (decision : Decision) (seq : Bytes) :
    (complete decision seq).scan = .ground := by
  cases decision <;> rfl

/-- Any complete CSI outside the owned table is emitted exactly once. -/
theorem step_csi_unowned (v : Vt) (rev : Bytes) (b : UInt8)
    (he : b ≠ ESC) (hf : 0x40 ≤ b ∧ b ≤ 0x7E)
    (hc : classifyCsi v (b :: rev).reverse = .unowned) :
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
      { scan := .ground, visible := [],
        replies := xtgetcapReply payloadRev.reverse } := by
  simp [Scan.step, complete]

/-- DECRQSS is negative for every selector and emits no selector bytes. -/
theorem step_decrqss (v : Vt) (payloadRev : Bytes) :
    (Scan.dcs 0x24 payloadRev true).step v STFinal =
      { scan := .ground, visible := [], replies := decrqssReply } := by
  simp [Scan.step, complete]

/-! ## Stream laws -/

/-- Full §Chunk law: re-chunking preserves the final VT and scanner, and
concatenates visible bytes and child replies in order. -/
theorem feed_append (v : Vt) (s : Scan) (a b : Bytes) :
    feed v s (a ++ b) =
      let first := feed v s a
      let second := feed first.vt first.scan b
      { vt := second.vt, scan := second.scan,
        visible := first.visible ++ second.visible,
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
      (feed v s a).visible ++
        (feed (feed v s a).vt (feed v s a).scan b).visible := by
  rw [feed_append]

theorem feed_append_replies (v : Vt) (s : Scan) (a b : Bytes) :
    (feed v s (a ++ b)).replies =
      (feed v s a).replies ++
        (feed (feed v s a).vt (feed v s a).scan b).replies := by
  rw [feed_append]

theorem feed_append_scan (v : Vt) (s : Scan) (a b : Bytes) :
    (feed v s (a ++ b)).scan =
      (feed (feed v s a).vt (feed v s a).scan b).scan := by
  rw [feed_append]

/-- The mediator observes every byte but does not alter emulator semantics. -/
theorem feed_vt (v : Vt) (s : Scan) (bytes : Bytes) :
    (feed v s bytes).vt = v.feed bytes := by
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
  | b :: bs =>
      (escSeen && b == STFinal) = false ∧ StFree (b == ESC) bs

/-- ESC-flag state after consuming a terminator-free body. -/
def escAfter : Bool → Bytes → Bool
  | escSeen, [] => escSeen
  | _, b :: bs => escAfter (b == ESC) bs

/-- A passthrough string body is emitted byte-for-byte, produces no reply,
and retains only its one-bit ESC flag. -/
theorem feed_strPass_free (v : Vt) (escSeen : Bool) (body : Bytes)
    (h : StFree escSeen body) :
    let r := feed v (.strPass escSeen) body
    r.scan = .strPass (escAfter escSeen body) ∧
      r.visible = body ∧ r.replies = [] := by
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
theorem feed_strPass_st (v : Vt) (escSeen : Bool) (body : Bytes)
    (h : StFree escSeen body) :
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
  rw [show [ESC, 0x5F] ++ payload ++ [ESC, STFinal] =
    [ESC, 0x5F] ++ (payload ++ [ESC, STFinal]) from rfl]
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
  rw [show [ESC, 0x50, 0x71] ++ payload ++ [ESC, STFinal] =
    [ESC, 0x50, 0x71] ++ (payload ++ [ESC, STFinal]) from rfl]
  dsimp only
  rw [feed_append]
  simp only at hp ⊢
  simp [feed, Scan.step, ESC, STFinal, hp]

/-! ## Scanner bound -/

/-- One byte preserves the candidate-buffer caps. -/
theorem Scan.Bounded.step {s : Scan} {v : Vt} {b : UInt8}
    (h : s.Bounded) : (s.step v b).scan.Bounded := by
  cases s <;> unfold Scan.step <;> dsimp only
  all_goals repeat' split
  all_goals simp_all [Scan.Bounded, Scan.pending, complete_scan,
    Nat.succ_le_iff, csiCap, oscCap, dcsCap]
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
theorem finish_exact (s : Scan) : finish s = (s.pending, .ground) := rfl

theorem finish_bounded (s : Scan) : (finish s).2.Bounded := by
  simp [finish, Scan.Bounded]

end Zmx.Core.Terminal
