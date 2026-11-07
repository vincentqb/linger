module

public import Linger.Session.Spec

public section

/-! # Linger.Session.Wire — the client ↔ daemon protocol

One frame = 1 tag byte + 4 length bytes (LE u32) + payload. The codec
works on `List UInt8` so the theorems in `Linger/Session/Proofs/Wire.lean` are
schema-level inductions, not fixtures; the runtime converts to/from
`ByteArray` at the socket boundary only.

Tensions carried here (see THEOREMS.md):
* §Frame — round-trip, and unknown tags are *values*, not errors.
* §Chunk — `Decoder.feed` is invariant under re-chunking.
* §Bound — a decoder never holds more than `4 + maxPayload` bytes; an
  oversize frame flips it into a sticky error state instead of growing.
-/

namespace Linger.Session.Wire

/-! ## u32 ↔ 4 LE bytes, via Nat so `omega` can chew the round-trip -/

/-- Four bytes, least significant first; `readU32` inverts it (`readU32_writeU32`). -/
def writeU32 (n : UInt32) : List UInt8 :=
  let v := n.toNat
  [UInt8.ofNat (v % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v / 65536 % 256),
    UInt8.ofNat (v / 16777216 % 256)]

/-- Total: missing bytes read as zero (a short structured payload is a
peer bug; reading zeros beats crashing — §Frame totality). -/
private def readU32 (l : List UInt8) : UInt32 :=
  let b := fun i => (l[i]?.getD 0).toNat
  UInt32.ofNat (b 0 + 256 * (b 1 + 256 * (b 2 + 256 * b 3)))

/-! ## Tag assignment (frozen; new tags append, old values never reused) -/

/-- A message's frame tag: 0 to 17 for the assigned messages, and an `unknown` message's
own tag. -/
private def Msg.tag : Msg → UInt8
  | .input _ => 0
  | .output _ => 1
  | .resize _ _ => 2
  | .attach _ _ => 3
  | .detachAll => 4
  | .kill => 5
  | .info => 6
  | .infoReply _ => 7
  | .history => 8
  | .exited _ => 9
  | .wait => 10
  | .labelSet _ => 11
  | .labelUnset _ => 12
  | .labelClear => 13
  | .done => 14
  | .err _ => 15
  | .screen => 16
  | .ended _ => 17
  | .unknown t _ => t

/-- Tags with an assigned meaning in this version. -/
private def knownTag (t : UInt8) : Bool := t ≤ 17

/-- An ending as two bytes: its kind (0 exited, 1 signalled, 2 unknown) and its code or signal
number. `readOutcome` inverts it (`readOutcome_outcomeBytes`). -/
private def outcomeBytes : Outcome → List UInt8
  | .exited code => [0, code]
  | .signaled signal => [1, signal]
  | .unknown => [2, 0]

/-- Total: a payload that is no ending this version knows reads as `unknown`, so a newer
daemon's ending is never misreported as an exit code or a signal. -/
private def readOutcome : List UInt8 → Outcome
  | 0 :: code :: _ => .exited code
  | 1 :: signal :: _ => .signaled signal
  | _ => .unknown

/-- A message's frame payload: the raw bytes it carries, its sizes or exit status through
`writeU32`, an ending's two bytes, or nothing. `decodeMsg` recovers a well-formed message from
its tag and payload (`decodeMsg_roundtrip`). -/
private def Msg.payload : Msg → List UInt8
  | .input b | .output b | .infoReply b | .err b | .labelSet b | .labelUnset b => b
  | .resize c r | .attach c r => writeU32 c ++ writeU32 r
  | .exited s => writeU32 s
  | .ended o => outcomeBytes o
  | .detachAll | .kill | .info | .history | .wait | .labelClear | .done | .screen => []
  | .unknown _ p => p

/-- Interpret one frame. Total: every (tag, payload) is some `Msg`.
An if-chain rather than a literal match so fall-through to `unknown`
is provable by `t ≠ 0, …, t ≠ 17` instead of match-compilation facts. -/
private def decodeMsg (tag : UInt8) (p : List UInt8) : Msg :=
  if tag = 0 then .input p
  else
    if tag = 1 then .output p
    else
      if tag = 2 then .resize (readU32 p) (readU32 (p.drop 4))
      else
        if tag = 3 then .attach (readU32 p) (readU32 (p.drop 4))
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
                        if tag = 11 then .labelSet p
                        else
                          if tag = 12 then .labelUnset p
                          else
                            if tag = 13 then .labelClear
                            else
                              if tag = 14 then .done
                              else
                                if tag = 15 then .err p
                                else
                                  if tag = 16 then .screen
                                  else if tag = 17 then .ended (readOutcome p) else .unknown tag p

/-- A message the encoder may legally emit: payload within §Bound, and
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
chunk). Structural recursion rather than a `foldl` so the §Stream
induction steps through it directly. -/
private def Decoder.feedAll (d : Decoder) : List (List UInt8) → Decoder × List Msg
  | [] => (d, [])
  | c :: cs =>
    let r := d.feed c
    let rest := r.1.feedAll cs
    (rest.1, r.2 ++ rest.2)

end Linger.Session.Wire
