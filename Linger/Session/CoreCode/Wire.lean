module

public import Linger.Session.CoreSpec

public section

/-! # Linger.Session.Wire — the client ↔ daemon protocol

One frame = 1 tag byte + 4 length bytes (LE u32) + payload. The codec
works on `List UInt8` so the theorems in `Linger/Session/Proofs/Wire.lean` are
schema-level inductions, not fixtures; the runtime converts to/from
`ByteArray` at the socket boundary only.

What the codec keeps:
* The round trip — a well-formed message decodes as itself, and unknown tags are *values*,
  not errors.
* Re-chunking invariance — `Decoder.feed` is invariant under re-chunking; with the round
  trip, re-chunked well-formed messages decode exactly (`decode_encode_chunked`,
  `Challenge.lean` part 1).
* The decoder bound — a decoder never holds more than `4 + maxPayload` bytes; an
  oversize frame flips it into a sticky error state instead of growing.
* Protocol levels — a client attaches only to a daemon that reports this version's protocol
  level (`admits_level`, part 5).
-/

namespace Linger.Session.Wire

/-! ## u32 ↔ 4 LE bytes, via Nat so `omega` can chew the round-trip -/

/-- Four bytes, least significant first; `readU32` inverts it (`readU32_writeU32`). -/
def writeU32 (n : UInt32) : List UInt8 :=
  let v := n.toNat
  [UInt8.ofNat (v % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v / 65536 % 256),
    UInt8.ofNat (v / 16777216 % 256)]

/-- Total: missing bytes read as zero (a short structured payload is a
peer bug; reading zeros beats crashing, and keeps decoding total). -/
private def readU32 (l : List UInt8) : UInt32 :=
  let b := fun i => (l[i]?.getD 0).toNat
  UInt32.ofNat (b 0 + 256 * (b 1 + 256 * (b 2 + 256 * b 3)))

/-! ## Tag assignment (frozen; new tags append, old values never reused)

Tag 3 was the attach of levels 1 and 2, which carried only a size and made a client that gave
none read-only. It is retired, so this version reads it as a message it does not know, and
refuses it, as an older daemon refuses tag 18, the attach that carries a mode. Tags 11 to 13 set,
removed and cleared labels before the session record had fields of its own; they are retired too,
and tag 21 describes the session. -/

/-- A message's frame tag: 0 to 21 for the assigned messages, but 3 and 11 to 13, which are
retired, and an `unknown` message's own tag. -/
private def Msg.tag : Msg → UInt8
  | .input _ => 0
  | .output _ => 1
  | .resize _ _ => 2
  | .attach _ _ _ => 18
  | .detachAll => 4
  | .kill => 5
  | .info => 6
  | .infoReply _ => 7
  | .history => 8
  | .exited _ => 9
  | .wait => 10
  | .done => 14
  | .err _ => 15
  | .screen => 16
  | .ended _ => 17
  | .saved _ => 19
  | .upgrade _ => 20
  | .describe _ => 21
  | .unknown t _ => t

/-- Tags with an assigned meaning in this version. -/
private def knownTag (t : UInt8) : Bool := t ≤ 21 && t != 3 && (t < 11 || 13 < t)

/-- A mode as one byte: 0 writable, 1 read-only. `readMode` inverts it (`readMode_modeByte`). -/
def modeByte : Mode → UInt8
  | .writable => 0
  | .readOnly => 1

/-- The mode a byte names, if this version knows it. An attach whose mode it does not know, as a
newer client's could be, is a message it cannot serve, so it is refused rather than read as
another mode. -/
def readMode (b : UInt8) : Option Mode :=
  if b = 0 then some .writable else if b = 1 then some .readOnly else none

/-- An ending as two bytes: its kind (0 exited, 1 signalled, 2 unknown) and its code or signal
number. `readOutcome` inverts it (`readOutcome_outcomeBytes`). -/
def outcomeBytes : Outcome → List UInt8
  | .exited code => [0, code]
  | .signaled signal => [1, signal]
  | .unknown => [2, 0]

/-- Total: a payload that is no ending this version knows reads as `unknown`, so a newer
daemon's ending is never misreported as an exit code or a signal. -/
def readOutcome : List UInt8 → Outcome
  | 0 :: code :: _ => .exited code
  | 1 :: signal :: _ => .signaled signal
  | _ => .unknown

/-- A message's frame payload: the raw bytes it carries, its sizes or exit status through
`writeU32`, after an attach's mode byte, an ending's two bytes, a signal's number, or nothing.
`decodeMsg` recovers a well-formed message from its tag and payload (`decodeMsg_roundtrip`). -/
private def Msg.payload : Msg → List UInt8
  | .input b | .output b | .infoReply b | .err b | .upgrade b | .describe b => b
  | .resize c r => writeU32 c ++ writeU32 r
  | .attach m c r => modeByte m :: (writeU32 c ++ writeU32 r)
  | .exited s => writeU32 s
  | .ended o => outcomeBytes o
  | .saved signal => [signal]
  | .detachAll | .kill | .info | .history | .wait | .done | .screen => []
  | .unknown _ p => p

/-- The attach a tag-18 payload carries: its mode byte, then the size, or `unknown` when the
payload names no mode this version knows. -/
private def decodeAttach (p : List UInt8) : Msg :=
  match p.head?.bind readMode with
  | some mode => .attach mode (readU32 (p.drop 1)) (readU32 (p.drop 5))
  | none => .unknown 18 p

/-- Interpret one frame. Total: every (tag, payload) is some `Msg`; a saved session's payload
reads its first byte as the signal, 0 when there is none. An if-chain rather than a literal match
so fall-through to `unknown` is provable by `t ≠ 0, …, t ≠ 19` instead of match-compilation
facts. -/
private def decodeMsg (tag : UInt8) (p : List UInt8) : Msg :=
  if tag = 0 then .input p
  else
    if tag = 1 then .output p
    else
      if tag = 2 then .resize (readU32 p) (readU32 (p.drop 4))
      else
        if tag = 4 then .detachAll
        else
          if tag = 5 then .kill
          else
            if tag = 6 then .info
            else
              if tag = 7 then .infoReply p
              else
                if tag = 8 then .history
                else
                  if tag = 9 then .exited (readU32 p)
                  else
                    if tag = 10 then .wait
                    else
                      if tag = 14 then .done
                      else
                        if tag = 15 then .err p
                        else
                          if tag = 16 then .screen
                          else
                            if tag = 17 then .ended (readOutcome p)
                            else
                              if tag = 18 then decodeAttach p
                              else
                                if tag = 19 then .saved (p.headD 0)
                                else
                                  if tag = 20 then .upgrade p
                                  else if tag = 21 then .describe p else .unknown tag p

/-- A message the encoder may legally emit: payload within `maxPayload`, and
`unknown` only for genuinely unassigned tags (an `unknown` wearing a
known tag would decode as the known message — nothing may build one). -/
def Msg.WF (m : Msg) : Prop :=
  m.payload.length ≤ maxPayload ∧
    match m with
    | .unknown t _ => knownTag t = false
    | _ => True

/-- One frame: tag byte, LE length, payload. -/
def encode (m : Msg) : List UInt8 := m.tag :: writeU32 (UInt32.ofNat m.payload.length) ++ m.payload

/-! ## Incremental decoder -/

/-- Greedily peel complete frames off `bytes`. Returns
(remaining-partial-bytes, errored, messages in arrival order). -/
private def takeFrames (bytes : List UInt8) : List UInt8 × Bool × List Msg :=
  match bytes with
  | t :: l0 :: l1 :: l2 :: l3 :: rest =>
    let len := (readU32 [l0, l1, l2, l3]).toNat
    if len > maxPayload then ([], true, [])
    else
      let payload := rest.take len
      if payload.length < len then (bytes, false, [])
      else
        let (buf, err, msgs) := takeFrames (rest.drop len)
        (buf, err, decodeMsg t payload :: msgs)
  | _ => (bytes, false, [])
termination_by bytes.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Feed a chunk. Emits every message completed by it. No-op once errored. -/
def Decoder.feed (d : Decoder) (chunk : List UInt8) : Decoder × List Msg :=
  if d.errored then (d, [])
  else
    let (buf, err, msgs) := takeFrames (d.buf ++ chunk)
    ({ buf, errored := err }, msgs)

/-- Decode a whole stream from scratch (specification form of `feed`). -/
private def decode (bytes : List UInt8) : Decoder × List Msg := Decoder.feed {} bytes

/-- Feed many chunks in sequence, concatenating the decoded messages —
the specification of the runtime's read loop (each poll round feeds one
chunk). Structural recursion rather than a `foldl` so the induction of
`Decoder.feedAll_flatten` steps through it directly. -/
private def Decoder.feedAll (d : Decoder) : List (List UInt8) → Decoder × List Msg
  | [] => (d, [])
  | c :: cs =>
    let r := d.feed c
    let rest := r.1.feedAll cs
    (rest.1, r.2 ++ rest.2)

/-! ## Input frames

`send` hands a session's program text of any length: the daemon refuses a frame whose payload
passes `maxPayload` and drops its connection, so the text travels in frames of `inputChunk`
bytes, as `send -` reads its standard input. -/

/-- The most bytes one `.input` frame of `send` carries: one read of `send -`'s standard input,
a quarter of `maxPayload`. -/
def inputChunk : Nat := 65536

/-- `bytes` in runs of `inputChunk` bytes, in order, the last one shorter, and none for no
bytes. -/
def inputChunks (bytes : List UInt8) : List (List UInt8) :=
  match bytes with
  | [] => []
  | b :: rest => (b :: rest).take inputChunk :: inputChunks ((b :: rest).drop inputChunk)
termination_by bytes.length
decreasing_by simp only [List.length_drop, List.length_cons, inputChunk]; omega

/-- The `.input` frames that carry `bytes` to a session's program, in order, each within the
decoder's cap (`inputFrames_exact`): `send` sends its text and each read of its standard input
this way. -/
def inputFrames (bytes : List UInt8) : List Msg := (inputChunks bytes).map .input

/-! ## Protocol levels

A daemon's `info` answer reports the protocol level it speaks. An attach goes only to a daemon
at this version's level, and refuses one of any earlier level: a daemon of level 1 or 2 refuses
this version's attach as a message it does not know, one of level 3 never says that a signal
stopped it, and one from before the level was reported drops the attach without a reply, so an
attach sent without asking would end in a bare refusal, a lost connection or a wait for the
detach key. -/

/-- Whether a client attaches to a daemon whose `info` answer reports protocol `level`, `none`
for an answer that reports no level, or for no answer: exactly when `level` is this version's,
`protocol` (`admits_iff`). -/
def admits (level : Option Nat) : Bool := level == some protocol

end Linger.Session.Wire
