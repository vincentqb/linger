module

public import Linger.App.CoreSpec
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Base64
import all Linger.Os.CoreCode.Json
import all Linger.App.CoreCode.Serve
import all Linger.App.Proofs.Serve
import all Linger.Session.Proofs.Wire
import all Linger.Session.CoreCode.Wire

/-! # A session's terminal as bytes: the stream carries exactly what an attach client writes

What `serve`'s base64 encoder writes, its decoder reads back. A read of an attach's connection adds
to what waits for the subscriber exactly the bytes an attach client writes of the messages the
read's bytes end, the first read answers the attach's request, and once a message ends the attach,
or the framing breaks, the stream's last update carries what waited and `closed`; a free writer
sends what waits, as one update whose `data` decodes to it, and then nothing waits. A screen an
attach shows, an ended session's or a read-only attach's of a saved one, is read as its output
frames (`paint`), which leave exactly its bytes waiting; and when the attach ends, one not yet
opened answers its request with what it found, and an open one's last update carries what waits
and `closed`, with the answer and code of what it found. -/

namespace Linger.App.Serve

/-! ## Base64 -/

/-- The characters of the padded base64 of `bytes`. -/
def Base64.chars : List UInt8 → List Char
  | a :: b :: c :: rest =>
    Base64.char (a.toNat / 4) ::
      Base64.char (a.toNat % 4 * 16 + b.toNat / 16) ::
      Base64.char (b.toNat % 16 * 4 + c.toNat / 64) ::
      Base64.char (c.toNat % 64) :: Base64.chars rest
  | [a, b] =>
    [Base64.char (a.toNat / 4), Base64.char (a.toNat % 4 * 16 + b.toNat / 16),
      Base64.char (b.toNat % 16 * 4), '=']
  | [a] => [Base64.char (a.toNat / 4), Base64.char (a.toNat % 4 * 16), '=', '=']
  | [] => []

/-- What the encoder writes after `out` is `out`, then the base64 of the bytes. -/
theorem Base64.encodeTo_toList :
    ∀ (out : String) (bytes : List UInt8),
      (Base64.encodeTo out bytes).toList = out.toList ++ Base64.chars bytes
  | out, a :: b :: c :: rest => by
    unfold Base64.encodeTo
    rw [Base64.encodeTo_toList _ rest]
    simp [String.toList_push, Base64.chars]
  | out, [a, b] => by simp [Base64.encodeTo, String.toList_push, Base64.chars]
  | out, [a] => by simp [Base64.encodeTo, String.toList_push, Base64.chars]
  | out, [] => by simp [Base64.encodeTo, Base64.chars]

/-- Each base64 digit reads back as its value. -/
theorem Base64.digit_char_fin : ∀ n : Fin 64, Base64.digit (Base64.char n.val) = some n.val := by
  decide

/-- No base64 digit is the padding character. -/
theorem Base64.char_ne_pad_fin : ∀ n : Fin 64, Base64.char n.val ≠ '=' := by decide

/-- The base64 digit of a value below 64 reads back as the value. -/
theorem Base64.digit_char {n : Nat} (h : n < 64) : Base64.digit (Base64.char n) = some n :=
  Base64.digit_char_fin ⟨n, h⟩

/-- The base64 digit of a value below 64 is no padding. -/
theorem Base64.char_ne_pad {n : Nat} (h : n < 64) : Base64.char n ≠ '=' :=
  Base64.char_ne_pad_fin ⟨n, h⟩

/-- The base64 of bytes decodes to the bytes. -/
theorem Base64.decode_chars : ∀ bytes : List UInt8, Base64.decode (Base64.chars bytes) = some bytes
  | a :: b :: c :: rest => by
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    have h1 : a.toNat / 4 < 64 := by omega
    have h2 : a.toNat % 4 * 16 + b.toNat / 16 < 64 := by omega
    have h3 : b.toNat % 16 * 4 + c.toNat / 64 < 64 := by omega
    have h4 : c.toNat % 64 < 64 := by omega
    simp only [Base64.chars]
    rw [Base64.decode.eq_4 _ _ _ _ _ (fun _ d _ => Base64.char_ne_pad h4 d) fun d _ =>
        Base64.char_ne_pad h4 d]
    simp only [Base64.digit_char h1, Base64.digit_char h2, Base64.digit_char h3,
      Base64.digit_char h4, Base64.decode_chars rest]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp [UInt8.toNat_ofNat] <;> omega
  | [a, b] => by
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have h1 : a.toNat / 4 < 64 := by omega
    have h2 : a.toNat % 4 * 16 + b.toNat / 16 < 64 := by omega
    have h3 : b.toNat % 16 * 4 < 64 := by omega
    simp only [Base64.chars]
    rw [Base64.decode.eq_3 _ _ _ (Base64.char_ne_pad h3)]
    simp only [Base64.digit_char h1, Base64.digit_char h2, Base64.digit_char h3]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp [UInt8.toNat_ofNat] <;> omega
  | [a] => by
    have ha := a.toNat_lt
    have h1 : a.toNat / 4 < 64 := by omega
    have h2 : a.toNat % 4 * 16 < 64 := by omega
    simp only [Base64.chars]
    rw [Base64.decode.eq_2]
    simp only [Base64.digit_char h1, Base64.digit_char h2]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      List.cons.injEq, and_true]
    apply UInt8.toNat_inj.mp
    simp [UInt8.toNat_ofNat]
    omega
  | [] => by simp [Base64.chars, Base64.decode]

/-- **What `serve` encodes in base64, `Base64.decode` reads back.** -/
theorem Base64.decode_encode (bytes : List UInt8) :
    Base64.decode (Base64.encode bytes).toList = some bytes := by
  rw [Base64.encode, Base64.encodeTo_toList]
  simpa using Base64.decode_chars bytes

/-! ## The stream -/

/-- An update of an attach's stream carries its bytes, with members after them or none. -/
theorem Output.update_carries (id : Id) (bytes : List UInt8) (more : List (String × Json)) :
    Carries id bytes ((Output.update id bytes).withMembers more) := by
  refine
    ⟨(output_update_names id bytes more).1, Base64.encode bytes, ?_, Base64.decode_encode bytes⟩
  simp [Output.update, Json.withMembers, Json.member?, List.lookup]

/-- An update of an attach's stream with no member after its own is itself. -/
theorem Output.update_withMembers_nil (id : Id) (bytes : List UInt8) :
    (Output.update id bytes).withMembers [] = Output.update id bytes := by
  simp [Output.update, Json.withMembers]

/-- An update of an attach's stream that the stream's end adds no member to carries no `closed`. -/
theorem Output.update_open (id : Id) (bytes : List UInt8) :
    (Output.update id bytes).member? "closed" = none := by
  simp [Output.update, Json.member?, List.lookup]

/-- The stream's last update carries `closed`. -/
theorem Output.update_closed (id : Id) (bytes : List UInt8) (found : Api.Found) :
    (((Output.update id bytes).withMembers (closedMembers found)).member? "closed").isSome := by
  simp [Output.update, Json.withMembers, Json.member?, List.lookup, closedMembers]

/-- **A read of an attach's connection is `Streamed`**, for an attach the connection holds. -/
theorem streamed_spec (s : State) (id : Id) (dec : Session.Wire.Decoder)
    (pending bytes : List UInt8) (held : (s.watching id).isSome) :
    Streamed Session.Wire.Decoder.feed id dec pending bytes (streamed s id dec pending bytes).2
      ((streamed s id dec pending bytes).1.watching id) := by
  unfold Streamed
  split
  · rename_i broken
    simp only [streamed, broken, ↓reduceIte, dropWatch_watching]
    exact ⟨by simp, _, rfl, Output.update_carries id _ _, Output.update_closed id _ _⟩
  · rename_i whole
    split
    · rename_i ends
      simp only [streamed, whole, ends, Bool.false_eq_true, ↓reduceIte, dropWatch_watching]
      exact ⟨by simp, _, rfl, Output.update_carries id _ _, Output.update_closed id _ _⟩
    · rename_i going
      simp only [streamed, whole, going, Bool.false_eq_true, ↓reduceIte, setWatch_watching]
      obtain ⟨w, holds⟩ := Option.isSome_iff_exists.mp held
      simp [holds]

/-- A free writer sends an open attach what waits for its subscriber, as one update with no
`closed`, and then nothing waits. -/
theorem flush_stream (s : State) (version : String) (id : Id) (dec : Session.Wire.Decoder)
    (pending : List UInt8) (ready : s.phase = .ready version)
    (holds : s.watching id = some (.stream dec pending)) :
    (step s (.flush id)).2 =
        (if pending = [] then []
        else [.send (.notify "session/output" (Output.update id pending))]) ∧
      (step s (.flush id)).1.watching id = some (.stream dec []) := by
  refine ⟨?_, ?_⟩ <;> simp [step, flushed, ready, holds, setWatch_watching]

/-- **The first read of an attach answers its request `done`**, and is streamed as every read
is. -/
theorem read_attaching (s : State) (version : String) (id : Id) (bytes : List UInt8)
    (ready : s.phase = .ready version) (asked : s.watching id = some .attaching) :
    step s (.read id bytes) =
      ((streamed s id {} [] bytes).1,
        .send (.result id (result .done [])) :: (streamed s id {} [] bytes).2) := by
  simp [step, readAttach, ready, asked]

/-- A later read of an attach is streamed. -/
theorem read_stream (s : State) (version : String) (id : Id) (dec : Session.Wire.Decoder)
    (pending bytes : List UInt8) (ready : s.phase = .ready version)
    (holds : s.watching id = some (.stream dec pending)) :
    step s (.read id bytes) = streamed s id dec pending bytes := by
  simp [step, readAttach, ready, holds]

/-! ## A shown screen -/

/-- An attach client writes all of the bytes output frames carry, then what follows. -/
theorem shown_outputFrames (bytes : List UInt8) (rest : List Session.Wire.Msg) :
    Session.Wire.shown (Remote.outputFrames bytes ++ rest) = bytes ++ Session.Wire.shown rest := by
  unfold Remote.outputFrames
  conv =>
    rhs; rw [← Session.Wire.inputChunks_flatten bytes]
  induction Session.Wire.inputChunks bytes with
  | nil => simp
  | cons chunk chunks ih => simp [Session.Wire.shown, ih]

/-- Output frames fit a frame. -/
theorem outputFrames_fit (bytes : List UInt8) : ∀ m ∈ Remote.outputFrames bytes, m.Fits := by
  intro m member
  simp only [Remote.outputFrames, List.mem_map] at member
  obtain ⟨chunk, inChunks, rfl⟩ := member
  have short := Session.Wire.inputChunks_length_le bytes chunk inChunks
  simp only [Session.Wire.Msg.Fits, Session.Wire.maxPayload]
  simp only [Session.Wire.inputChunk] at short
  omega

/-- No output frame ends an attach. -/
theorem outputFrames_ends (bytes : List UInt8) :
    (Remote.outputFrames bytes).any Session.Wire.Msg.ends = false := by
  simp [Remote.outputFrames, Session.Wire.Msg.ends]

/-- **A shown screen's read decodes to the screen's output frames**, as an attach client decodes
it, and leaves the decoder as it started. -/
theorem feed_paint (screen : List UInt8) :
    Session.Wire.Decoder.feed {} (paint screen) =
      ({ buf := [], errored := false }, Remote.outputFrames screen) := by
  have decoded :=
    Session.Wire.decode_encode_stream (Remote.outputFrames screen)
      (fun m member => Session.Wire.fits_wf m (outputFrames_fit screen m member))
  exact decoded

/-- **A shown screen's read answers the attach's request `done`**, and leaves exactly the
screen's bytes waiting for its subscriber. -/
theorem read_paint (s : State) (version : String) (id : Id) (screen : List UInt8)
    (ready : s.phase = .ready version) (asked : s.watching id = some .attaching) :
    (step s (.read id (paint screen))).2 = [.send (.result id (result .done []))] ∧
      (step s (.read id (paint screen))).1.watching id = some (.stream {} screen) := by
  have shown := shown_outputFrames screen []
  simp only [Session.Wire.shown, List.append_nil] at shown
  rw [read_attaching s version id (paint screen) ready asked]
  simp [streamed, feed_paint, outputFrames_ends, shown, setWatch_watching, asked]

/-! ## The attach's end -/

/-- **An attach that ends before it opened answers its request** with what it found and what it
said, and is held no more. -/
theorem unwatched_attaching (s : State) (version : String) (id : Id) (found : Api.Found)
    (said : Log String) (ready : s.phase = .ready version)
    (asked : s.watching id = some .attaching) :
    (step s (.unwatched id found said)).2 = [.send (.result id (result found (saidMembers said)))] ∧
      (step s (.unwatched id found said)).1.watching id = none := by
  refine ⟨?_, ?_⟩ <;> simp [step, unwatched, ready, asked, dropWatch_watching]

/-- **An open attach that ends sends its last update**, what waits and `closed` with what it found,
and is held no more. -/
theorem unwatched_stream (s : State) (version : String) (id : Id) (dec : Session.Wire.Decoder)
    (pending : List UInt8) (found : Api.Found) (said : Log String)
    (ready : s.phase = .ready version) (holds : s.watching id = some (.stream dec pending)) :
    (step s (.unwatched id found said)).2 =
        [.send
            (.notify "session/output"
              ((Output.update id pending).withMembers (closedMembers found)))] ∧
      (step s (.unwatched id found said)).1.watching id = none := by
  refine ⟨?_, ?_⟩ <;> simp [step, unwatched, ready, holds, dropWatch_watching]

/-- The last update's `closed` opens with the answer of what the attach found, and its code. -/
theorem update_closed_members (id : Id) (bytes : List UInt8) (found : Api.Found) :
    ∃ rest,
      ((Output.update id bytes).withMembers (closedMembers found)).member? "closed" =
        some
          (.obj
            (("answer", .str (answerName (Api.answer found))) ::
              ("code", .int (Os.Answer.code (Api.answer found)).toNat) :: rest)) := by
  obtain ⟨rest, members⟩ :
    ∃ rest,
      closedMembers found =
        [("closed",
            .obj
              (("answer", .str (answerName (Api.answer found))) ::
                ("code", .int (Os.Answer.code (Api.answer found)).toNat) :: rest))] :=
    ⟨_, rfl⟩
  exact ⟨rest, by simp [Output.update, Json.withMembers, Json.member?, List.lookup, members]⟩

/-- **An attach's stream is exact, for every session an attach reaches**: every read is
`Streamed`, the first answering the attach's request; a shown screen's read leaves exactly the
screen waiting; a free writer sends what waits, as one update without `closed`; and the attach's
end answers a request not yet answered with what it found, or sends the last update, which carries
what waits and `closed` with the answer and code of what it found. -/
theorem attach_stream (s : State) (version : String) (id : Id) (dec : Session.Wire.Decoder)
    (pending bytes screen : List UInt8) (found : Api.Found) (said : Log String)
    (ready : s.phase = .ready version) :
    AttachStream State.watching step result Api.answer Os.Answer.code paint
      Session.Wire.Decoder.feed s id dec pending bytes screen found said := by
  refine ⟨fun asked => ?_, fun holds => ?_⟩
  · obtain ⟨answered, dropped⟩ := unwatched_attaching s version id found said ready asked
    obtain ⟨painted, shown⟩ := read_paint s version id screen ready asked
    rw [read_attaching s version id bytes ready asked]
    exact
      ⟨⟨_, rfl, streamed_spec s id {} [] bytes (by simp [asked])⟩, painted, shown, ⟨_, answered⟩,
        dropped⟩
  · obtain ⟨last, dropped⟩ := unwatched_stream s version id dec pending found said ready holds
    obtain ⟨rest, closed⟩ := update_closed_members id pending found
    rw [read_stream s version id dec pending bytes ready holds]
    obtain ⟨sent, after⟩ := flush_stream s version id dec pending ready holds
    refine
      ⟨streamed_spec s id dec pending bytes (by simp [holds]), ?_, ?_, after,
        ⟨_, rest, last, Output.update_carries id pending (closedMembers found), closed⟩, dropped⟩
    · intro empty
      simp [sent, empty]
    · intro waiting
      have carries := Output.update_carries id pending []
      rw [Output.update_withMembers_nil] at carries
      exact ⟨_, by simp [sent, waiting], carries, Output.update_open id pending⟩

end Linger.App.Serve
