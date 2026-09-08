module

public import Linger.Core.Wire
import all Linger.Core.Wire

public section

/-! # §Frame / §Chunk / §Bound — the wire protocol theorems

THEOREMS.md rows: §Frame (round-trip; unknown tags are data),
§Chunk (re-chunking cannot change what a peer sees), §Bound (a decoder
holds at most `4 + maxPayload` bytes whatever a peer sends — the
anti-zellij invariant at the wire layer).

All statements are schema-level (∀ messages, ∀ chunkings), not
fixtures: the codec is `List UInt8`-based precisely so these inductions
go through by kernel reduction alone (no proof in this directory uses
the compiled-evaluation escape hatch; the e2e gate enforces it).
-/

namespace Linger.Core.Wire

/-! ## u32 codec -/

@[simp] theorem writeU32_length (n : UInt32) : (writeU32 n).length = 4 := by
  simp [writeU32]

@[simp] theorem readU32_writeU32 (n : UInt32) : readU32 (writeU32 n) = n := by
  have h := n.toNat_lt
  apply UInt32.toNat_inj.mp
  simp [readU32, writeU32, UInt8.toNat_ofNat', UInt32.toNat_ofNat']
  omega

/-- Reading a u32 sees only the first 4 bytes. -/
@[simp] theorem readU32_writeU32_append (n : UInt32) (rest : List UInt8) :
    readU32 (writeU32 n ++ rest) = n := by
  have h := n.toNat_lt
  apply UInt32.toNat_inj.mp
  simp [readU32, writeU32, UInt8.toNat_ofNat', UInt32.toNat_ofNat']
  omega

@[simp] theorem drop4_writeU32_append (n : UInt32) (rest : List UInt8) :
    (writeU32 n ++ rest).drop 4 = rest := by
  simp [writeU32]

/-! ## Single-message round-trip (§Frame) -/

/-- Re-interpreting a well-formed message's own tag and payload yields
the message back. `wf` is load-bearing in the `unknown` case: an
`unknown` wearing a known tag would decode as the known message, which
is why `wf` forbids constructing one. -/
theorem decodeMsg_roundtrip (m : Msg) (hm : m.wf) :
    decodeMsg m.tag m.payload = m := by
  cases m with
  | unknown t p =>
    have ht : ¬ t ≤ 16 := by simpa [knownTag] using hm.2
    have ne : ∀ (i : UInt8), i ≤ 16 → t ≠ i := fun i hi h => ht (h ▸ hi)
    simp [decodeMsg, Msg.tag, Msg.payload,
      ne 0 (by decide), ne 1 (by decide), ne 2 (by decide), ne 3 (by decide),
      ne 4 (by decide), ne 5 (by decide), ne 6 (by decide), ne 7 (by decide),
      ne 8 (by decide), ne 9 (by decide), ne 10 (by decide), ne 11 (by decide),
      ne 12 (by decide), ne 13 (by decide), ne 14 (by decide), ne 15 (by decide),
      ne 16 (by decide)]
  | _ => simp [decodeMsg, Msg.tag, Msg.payload]

/-! ## takeFrames, frame by frame -/

/-- A syntactically explicit header peels off in one step. -/
theorem takeFrames_header (t b0 b1 b2 b3 : UInt8) (payload rest : List UInt8)
    (hb : (readU32 [b0, b1, b2, b3]).toNat = payload.length)
    (hp : payload.length ≤ maxPayload) :
    takeFrames (t :: b0 :: b1 :: b2 :: b3 :: (payload ++ rest))
      = ((takeFrames rest).1, (takeFrames rest).2.1,
         decodeMsg t payload :: (takeFrames rest).2.2) := by
  have hle : payload.length ≤ payload.length := Nat.le_refl _
  rcases hres : takeFrames rest with ⟨buf, err, msgs⟩
  rw [takeFrames.eq_def]
  dsimp only
  rw [hb]
  rw [ite_eq_right (by omega)]
  rw [ite_eq_right (by rw [List.length_append]; omega)]
  rw [List.take_append_of_le_length hle, List.take_of_length_le (Nat.le_refl _),
      List.drop_append_of_le_length hle, List.drop_of_length_le (Nat.le_refl _),
      List.nil_append, hres]

/-- A well-formed encoded frame peels off `takeFrames`, whatever
follows it. The workhorse for §Frame and §Chunk alike. -/
theorem takeFrames_encode_prefix (m : Msg) (hm : m.wf) (rest : List UInt8) :
    takeFrames (encode m ++ rest)
      = ((takeFrames rest).1, (takeFrames rest).2.1, m :: (takeFrames rest).2.2) := by
  have hp : m.payload.length ≤ maxPayload := hm.1
  have hlt : m.payload.length < 4294967296 := by
    have he : maxPayload = 262144 := by rfl
    omega
  obtain ⟨b0, b1, b2, b3, hw⟩ :
      ∃ b0 b1 b2 b3, writeU32 (UInt32.ofNat m.payload.length) = [b0, b1, b2, b3] :=
    ⟨_, _, _, _, rfl⟩
  have hb : (readU32 [b0, b1, b2, b3]).toNat = m.payload.length := by
    rw [← hw, readU32_writeU32, UInt32.toNat_ofNat']
    omega
  have hshape : encode m ++ rest
      = m.tag :: b0 :: b1 :: b2 :: b3 :: (m.payload ++ rest) := by
    simp [encode, hw]
  rw [hshape, takeFrames_header m.tag b0 b1 b2 b3 m.payload rest hb hp,
      decodeMsg_roundtrip m hm]

@[simp] theorem takeFrames_nil : takeFrames [] = ([], false, []) := by
  rw [takeFrames.eq_def]

/-- §Frame: one well-formed message round-trips exactly. -/
theorem decode_encode (m : Msg) (hm : m.wf) :
    decode (encode m) = ({ buf := [], errored := false }, [m]) := by
  have h := takeFrames_encode_prefix m hm []
  simp only [takeFrames_nil, List.append_nil] at h
  simp [decode, Decoder.feed, h]

/-- §Frame, stream form: a sequence of well-formed messages decodes
back to itself exactly, with nothing retained. -/
theorem decode_encode_stream (ms : List Msg) (h : ∀ m ∈ ms, m.wf) :
    decode (ms.flatMap encode) = ({ buf := [], errored := false }, ms) := by
  suffices hs : takeFrames (ms.flatMap encode) = ([], false, ms) by
    simp [decode, Decoder.feed, hs]
  induction ms with
  | nil => simp
  | cons m ms ih =>
    have hm := h m (by simp)
    have hms := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons]
    rw [takeFrames_encode_prefix m hm, hms]

/-! ## §Chunk — re-chunking invariance -/

/-- Parsing a concatenation = parsing the first part, then parsing its
leftover glued to the second part. Errors and messages both carry. -/
theorem takeFrames_append (xs ys : List UInt8) :
    takeFrames (xs ++ ys)
      = (if (takeFrames xs).2.1 then ([], true, (takeFrames xs).2.2)
         else ((takeFrames ((takeFrames xs).1 ++ ys)).1,
               (takeFrames ((takeFrames xs).1 ++ ys)).2.1,
               (takeFrames xs).2.2 ++ (takeFrames ((takeFrames xs).1 ++ ys)).2.2)) := by
  induction xs using takeFrames.induct with
  | case1 t l0 l1 l2 l3 rest len hlen =>
    replace hlen : (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest) = ([], true, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_left hlen]
    have hy : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: (rest ++ ys)) = ([], true, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_left hlen]
    simp [hx, hy]
  | case2 t l0 l1 l2 l3 rest len hlen hshort =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (t :: l0 :: l1 :: l2 :: l3 :: rest, false, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_right hlen, ite_eq_left hshort]
    simp [hx]
  | case3 t l0 l1 l2 l3 rest len hlen hshort buf err msgs heq ih =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : ¬ rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hle : (readU32 [l0, l1, l2, l3]).toNat ≤ rest.length := Nat.le_of_not_lt hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (buf, err, decodeMsg t (rest.take (readU32 [l0, l1, l2, l3]).toNat) :: msgs) := by
      rw [takeFrames.eq_def]; dsimp only
      rw [ite_eq_right hlen, ite_eq_right hshort, heq]
    rcases h2 : takeFrames (rest.drop (readU32 [l0, l1, l2, l3]).toNat ++ ys)
      with ⟨buf2, err2, msgs2⟩
    have hy : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: (rest ++ ys))
        = (buf2, err2, decodeMsg t (rest.take (readU32 [l0, l1, l2, l3]).toNat) :: msgs2) := by
      rw [takeFrames.eq_def]; dsimp only
      rw [ite_eq_right hlen, ite_eq_right (by rw [List.length_append]; omega),
          List.take_append_of_le_length hle, List.drop_append_of_le_length hle, h2]
    rw [ih, heq] at h2
    by_cases he : err
    · simp [he] at h2
      obtain ⟨hb2, he2, hm2⟩ := h2
      subst hb2; subst he2; subst hm2
      simp [hx, hy, he]
    · simp [he] at h2
      obtain ⟨hb2, he2, hm2⟩ := h2
      subst hb2; subst he2; subst hm2
      simp [hx, hy, he]
  | case4 xs hno =>
    have hx : takeFrames xs = (xs, false, []) := by
      rw [takeFrames.eq_def]
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hno a b c d e tail)
    simp [hx]

/-- An errored parse retains nothing: the poisoned buffer is dropped,
not kept around. (Also what makes `feed_append` hold through errors.) -/
theorem takeFrames_errored_buf (bytes : List UInt8)
    (h : (takeFrames bytes).2.1 = true) : (takeFrames bytes).1 = [] := by
  induction bytes using takeFrames.induct with
  | case1 t l0 l1 l2 l3 rest len hlen =>
    replace hlen : (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest) = ([], true, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_left hlen]
    simp [hx]
  | case2 t l0 l1 l2 l3 rest len hlen hshort =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (t :: l0 :: l1 :: l2 :: l3 :: rest, false, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_right hlen, ite_eq_left hshort]
    rw [hx] at h
    simp at h
  | case3 t l0 l1 l2 l3 rest len hlen hshort buf err msgs heq ih =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : ¬ rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (buf, err, decodeMsg t (rest.take (readU32 [l0, l1, l2, l3]).toNat) :: msgs) := by
      rw [takeFrames.eq_def]; dsimp only
      rw [ite_eq_right hlen, ite_eq_right hshort, heq]
    rw [hx] at h ⊢
    rw [heq] at ih
    exact ih h
  | case4 xs hno =>
    have hx : takeFrames xs = (xs, false, []) := by
      rw [takeFrames.eq_def]
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hno a b c d e tail)
    rw [hx] at h
    simp at h

/-- §Chunk at the decoder interface: feeding `a ++ b` is feeding `a`
then feeding `b` — same final state, same messages in order. No
chunking of the byte stream can change what the peer sees. -/
theorem Decoder.feed_append (d : Decoder) (a b : List UInt8) :
    d.feed (a ++ b)
      = (((d.feed a).1.feed b).1, (d.feed a).2 ++ ((d.feed a).1.feed b).2) := by
  by_cases hd : d.errored
  · simp [Decoder.feed, hd]
  · rcases h1 : takeFrames (d.buf ++ a) with ⟨buf1, err1, msgs1⟩
    have hsplit := takeFrames_append (d.buf ++ a) b
    rw [h1] at hsplit
    by_cases he1 : err1
    · have hb1 : buf1 = [] := by
        have h' := takeFrames_errored_buf (d.buf ++ a)
        rw [h1] at h'
        exact h' (by simp [he1])
      subst hb1
      simp only [he1, ite_true] at hsplit
      simp [Decoder.feed, hd, h1, he1, ← List.append_assoc, hsplit]
    · simp only [he1] at hsplit
      rcases h2 : takeFrames (buf1 ++ b) with ⟨buf2, err2, msgs2⟩
      rw [h2] at hsplit
      simp [Decoder.feed, hd, h1, he1, h2, ← List.append_assoc, hsplit]

/-- Once errored, a decoder stays errored and emits nothing — the
runtime's cue to close the connection, and the reason a malformed peer
cannot make us buffer. -/
theorem Decoder.feed_errored (d : Decoder) (chunk : List UInt8) (hd : d.errored) :
    d.feed chunk = (d, []) := by
  simp [Decoder.feed, hd]

/-! ## §Bound — the decoder cannot be grown -/

/-- Whatever bytes arrive, the parser's retained buffer stays under
`5 + maxPayload` bytes: complete frames leave, a partial frame is by
definition smaller than one max-size frame, and an oversize claim
empties the buffer (error) rather than filling it. -/
theorem takeFrames_buf_le (bytes : List UInt8) :
    (takeFrames bytes).1.length ≤ 4 + maxPayload := by
  induction bytes using takeFrames.induct with
  | case1 t l0 l1 l2 l3 rest len hlen =>
    replace hlen : (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest) = ([], true, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_left hlen]
    simp [hx]
  | case2 t l0 l1 l2 l3 rest len hlen hshort =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (t :: l0 :: l1 :: l2 :: l3 :: rest, false, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_right hlen, ite_eq_left hshort]
    simp [hx]
    omega
  | case3 t l0 l1 l2 l3 rest len hlen hshort buf err msgs heq ih =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : ¬ rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (buf, err, decodeMsg t (rest.take (readU32 [l0, l1, l2, l3]).toNat) :: msgs) := by
      rw [takeFrames.eq_def]; dsimp only
      rw [ite_eq_right hlen, ite_eq_right hshort, heq]
    rw [heq] at ih
    simpa [hx] using ih
  | case4 xs hno =>
    have hx : takeFrames xs = (xs, false, []) := by
      rw [takeFrames.eq_def]
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hno a b c d e tail)
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩ <;>
      simp [hx, maxPayload]
    exact absurd rfl (hno _ _ _ _ _ _)

/-- §Bound at the decoder interface: after any feed to a live decoder,
the retained buffer is under `4 + maxPayload` bytes — regardless of the
decoder's prior state or the chunk's size or content. -/
theorem Decoder.feed_buf_le (d : Decoder) (chunk : List UInt8) (hd : ¬ d.errored) :
    ((d.feed chunk).1).buf.length ≤ 4 + maxPayload := by
  have h := takeFrames_buf_le (d.buf ++ chunk)
  rcases hres : takeFrames (d.buf ++ chunk) with ⟨buf, err, msgs⟩
  rw [hres] at h
  simp [Decoder.feed, hd, hres]
  exact h

/-- §Bound, message side: no decoded message carries a payload above
`maxPayload` — the state machines downstream never see an unbounded
allocation. -/
theorem decodeMsg_payload_le (t : UInt8) (p : List UInt8) (hp : p.length ≤ maxPayload) :
    (decodeMsg t p).payload.length ≤ maxPayload := by
  have h8 : (8 : Nat) ≤ maxPayload := by simp [maxPayload]
  have h4 : (4 : Nat) ≤ maxPayload := by simp [maxPayload]
  unfold decodeMsg
  -- In each positive branch, rewriting `t` to the literal collapses the
  -- whole if-chain, so only the current hypothesis is needed.
  by_cases h0 : t = 0
  · simp [h0, Msg.payload, hp]
  by_cases h1 : t = 1
  · simp [h1, Msg.payload, hp]
  by_cases h2 : t = 2
  · simp [h2, Msg.payload, h8]
  by_cases h3 : t = 3
  · simp [h3, Msg.payload, h8]
  by_cases h4' : t = 4
  · simp [h4', Msg.payload]
  by_cases h5 : t = 5
  · simp [h5, Msg.payload]
  by_cases h6 : t = 6
  · simp [h6, Msg.payload]
  by_cases h7 : t = 7
  · simp [h7, Msg.payload, hp]
  by_cases h8' : t = 8
  · simp [h8', Msg.payload]
  by_cases h9 : t = 9
  · simp [h9, Msg.payload, h4]
  by_cases h10 : t = 10
  · simp [h10, Msg.payload]
  by_cases h11 : t = 11
  · simp [h11, Msg.payload, hp]
  by_cases h12 : t = 12
  · simp [h12, Msg.payload, hp]
  by_cases h13 : t = 13
  · simp [h13, Msg.payload]
  by_cases h14 : t = 14
  · simp [h14, Msg.payload]
  by_cases h15 : t = 15
  · simp [h15, Msg.payload, hp]
  by_cases h16 : t = 16
  · simp [h16, Msg.payload]
  -- fall-through: every test is false, the result is `.unknown t p`
  simp [h0, h1, h2, h3, h4', h5, h6, h7, h8', h9, h10, h11, h12, h13, h14, h15, h16,
    Msg.payload, hp]

theorem takeFrames_msgs_payload_le (bytes : List UInt8) :
    ∀ m ∈ (takeFrames bytes).2.2, m.payload.length ≤ maxPayload := by
  induction bytes using takeFrames.induct with
  | case1 t l0 l1 l2 l3 rest len hlen =>
    replace hlen : (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest) = ([], true, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_left hlen]
    simp [hx]
  | case2 t l0 l1 l2 l3 rest len hlen hshort =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (t :: l0 :: l1 :: l2 :: l3 :: rest, false, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_right hlen, ite_eq_left hshort]
    simp [hx]
  | case3 t l0 l1 l2 l3 rest len hlen hshort buf err msgs heq ih =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : ¬ rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (buf, err, decodeMsg t (rest.take (readU32 [l0, l1, l2, l3]).toNat) :: msgs) := by
      rw [takeFrames.eq_def]; dsimp only
      rw [ite_eq_right hlen, ite_eq_right hshort, heq]
    rw [heq] at ih
    intro m hmem
    rw [hx] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · subst h
      apply decodeMsg_payload_le
      have := List.length_take_le (readU32 [l0, l1, l2, l3]).toNat rest
      omega
    · exact ih m h
  | case4 xs hno =>
    have hx : takeFrames xs = (xs, false, []) := by
      rw [takeFrames.eq_def]
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hno a b c d e tail)
    simp [hx]

/-! ## §Stream — chunking is invisible (§Frame ∘ §Chunk, composed)

The operational statement a reader actually wants, in one theorem:
however the transport fragments a well-formed encoded stream, the
receiver decodes exactly that stream. `decode_encode` and
`decode_encode_stream` are its one-message / one-chunk special cases.
-/

/-- A `takeFrames` leftover is quiescent: re-parsing it yields itself —
no messages, no error. (By construction it is less than one complete
frame.) -/
theorem takeFrames_leftover_stable (bytes : List UInt8) :
    takeFrames (takeFrames bytes).1 = ((takeFrames bytes).1, false, []) := by
  induction bytes using takeFrames.induct with
  | case1 t l0 l1 l2 l3 rest len hlen =>
    replace hlen : (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest) = ([], true, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_left hlen]
    simp [hx]
  | case2 t l0 l1 l2 l3 rest len hlen hshort =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (t :: l0 :: l1 :: l2 :: l3 :: rest, false, []) := by
      rw [takeFrames.eq_def]; dsimp only; rw [ite_eq_right hlen, ite_eq_left hshort]
    simp [hx]
  | case3 t l0 l1 l2 l3 rest len hlen hshort buf err msgs heq ih =>
    replace hlen : ¬ (readU32 [l0, l1, l2, l3]).toNat > maxPayload := hlen
    replace hshort : ¬ rest.length < (readU32 [l0, l1, l2, l3]).toNat := hshort
    have hx : takeFrames (t :: l0 :: l1 :: l2 :: l3 :: rest)
        = (buf, err, decodeMsg t (rest.take (readU32 [l0, l1, l2, l3]).toNat) :: msgs) := by
      rw [takeFrames.eq_def]; dsimp only
      rw [ite_eq_right hlen, ite_eq_right hshort, heq]
    rw [heq] at ih
    simpa [hx] using ih
  | case4 xs hno =>
    have hx : takeFrames xs = (xs, false, []) := by
      rw [takeFrames.eq_def]
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hno a b c d e tail)
    simp [hx]

/-- Feeding chunks one at a time equals feeding their concatenation —
for any decoder whose buffer is quiescent, which every decoder the feed
path produces is (and a fresh one trivially is). -/
theorem Decoder.feedAll_flatten (d : Decoder) (chunks : List (List UInt8))
    (hq : takeFrames d.buf = (d.buf, false, [])) :
    d.feedAll chunks = d.feed chunks.flatten := by
  induction chunks generalizing d with
  | nil =>
    by_cases he : d.errored
    · simp [Decoder.feedAll, Decoder.feed_errored d [] he]
    · rcases d with ⟨buf, err⟩
      simp only [Bool.not_eq_true] at he
      subst he
      simp [Decoder.feedAll, Decoder.feed, hq]
  | cons c cs ih =>
    -- the decoder after one feed is quiescent again
    have hq' : takeFrames (d.feed c).1.buf = ((d.feed c).1.buf, false, []) := by
      by_cases he : d.errored
      · rw [Decoder.feed_errored d c he]
        exact hq
      · rcases hres : takeFrames (d.buf ++ c) with ⟨buf1, err1, msgs1⟩
        have hb : (d.feed c).1.buf = buf1 := by
          simp [Decoder.feed, he, hres]
        rw [hb]
        by_cases he1 : err1 = true
        · have hb1 := takeFrames_errored_buf (d.buf ++ c) (by rw [hres]; simpa using he1)
          rw [hres] at hb1
          simp only at hb1
          simp [hb1]
        · have hst := takeFrames_leftover_stable (d.buf ++ c)
          rw [hres] at hst
          simpa using hst
    show (((d.feed c).1.feedAll cs).1, (d.feed c).2 ++ ((d.feed c).1.feedAll cs).2)
        = d.feed ((c :: cs).flatten)
    rw [List.flatten_cons, Decoder.feed_append, ih _ hq']

/-- §Stream: ANY well-formed message sequence, encoded and re-chunked
ARBITRARILY (per byte, per frame, any TCP segmentation), feeds back to
exactly that sequence — same messages, same order, nothing retained,
no error. -/
theorem decode_encode_chunked (ms : List Msg) (hms : ∀ m ∈ ms, m.wf)
    (chunks : List (List UInt8)) (hc : chunks.flatten = ms.flatMap encode) :
    Decoder.feedAll {} chunks = ({ buf := [], errored := false }, ms) := by
  rw [Decoder.feedAll_flatten _ _ (by simp), hc]
  simpa [decode] using decode_encode_stream ms hms

end Linger.Core.Wire
