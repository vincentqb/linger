/-! # Linger.Core.Wire — the client ↔ daemon protocol

One frame = 1 tag byte + 4 length bytes (LE u32) + payload. The codec
works on `List UInt8` so the theorems in `Theorems/Wire.lean` are
schema-level inductions, not fixtures; the runtime converts to/from
`ByteArray` at the socket boundary only.

Tensions carried here (see THEOREMS.md):
* §Frame — round-trip, and unknown tags are *values*, not errors.
* §Chunk — `Decoder.feed` is invariant under re-chunking.
* §Bound — a decoder never holds more than `4 + maxPayload` bytes; an
  oversize frame flips it into a sticky error state instead of growing.
-/

namespace Linger.Core.Wire

/-- Largest payload a frame may carry. Reads from the OS are ≤ 64 KiB
(`Linger.Posix.read`), so honest senders stay far below; a frame claiming
more is either corruption or an attack, and §Bound turns it into a
connection error rather than memory growth. -/
def maxPayload : Nat := 262144

/-- The message vocabulary. Payload-carrying constructors keep raw
bytes; numeric fields are encoded LE at the payload layer. `unknown`
makes the decoder total (§Frame): a tag from a newer peer is data. -/
inductive Msg where
  /-- client → daemon: bytes for the pty (keystrokes, pastes). -/
  | input (bytes : List UInt8)
  /-- daemon → client: bytes from the pty (also used for history/restore). -/
  | output (bytes : List UInt8)
  /-- client → daemon: my terminal is now cols×rows. -/
  | resize (cols rows : UInt32)
  /-- client → daemon: I am a live client; stream output to me. -/
  | attach (cols rows : UInt32)
  /-- client → daemon: disconnect every attached client (incl. me). -/
  | detachAll
  /-- client → daemon: terminate the session. -/
  | kill
  /-- client → daemon: describe yourself (one-shot). -/
  | info
  /-- daemon → client: `k\tv\n` lines (fields + labels). -/
  | infoReply (bytes : List UInt8)
  /-- client → daemon: send scrollback as output frames, then `done`. -/
  | history
  /-- daemon → client: the child exited with this status. -/
  | exited (status : UInt32)
  /-- client → daemon: hold this connection open until the child exits. -/
  | wait
  /-- client → daemon: set one `k=v` label. -/
  | labelSet (kv : List UInt8)
  /-- client → daemon: remove one label by key. -/
  | labelUnset (k : List UInt8)
  /-- client → daemon: remove all labels. -/
  | labelClear
  /-- daemon → client: end of a request/reply exchange. -/
  | done
  /-- daemon → client: request failed, human-readable reason. -/
  | err (msg : List UInt8)
  /-- any tag this version does not know: skipped, never fatal (§Frame). -/
  | unknown (tag : UInt8) (payload : List UInt8)
  deriving Repr, DecidableEq, Inhabited

/-! ## u32 ↔ 4 LE bytes, via Nat so `omega` can chew the round-trip -/

def writeU32 (n : UInt32) : List UInt8 :=
  let v := n.toNat
  [UInt8.ofNat (v % 256), UInt8.ofNat (v / 256 % 256),
   UInt8.ofNat (v / 65536 % 256), UInt8.ofNat (v / 16777216 % 256)]

/-- Total: missing bytes read as zero (a short structured payload is a
peer bug; reading zeros beats crashing — §Frame totality). -/
def readU32 (l : List UInt8) : UInt32 :=
  let b := fun i => (l[i]?.getD 0).toNat
  UInt32.ofNat (b 0 + 256 * (b 1 + 256 * (b 2 + 256 * b 3)))

/-! ## Tag assignment (frozen; new tags append, old values never reused) -/

def Msg.tag : Msg → UInt8
  | .input _      => 0
  | .output _     => 1
  | .resize _ _   => 2
  | .attach _ _   => 3
  | .detachAll    => 4
  | .kill         => 5
  | .info         => 6
  | .infoReply _  => 7
  | .history      => 8
  | .exited _     => 9
  | .wait         => 10
  | .labelSet _   => 11
  | .labelUnset _ => 12
  | .labelClear   => 13
  | .done         => 14
  | .err _        => 15
  | .unknown t _  => t

/-- Tags with an assigned meaning in this version. -/
def knownTag (t : UInt8) : Bool := t ≤ 15

def Msg.payload : Msg → List UInt8
  | .input b | .output b | .infoReply b | .err b
  | .labelSet b | .labelUnset b => b
  | .resize c r | .attach c r => writeU32 c ++ writeU32 r
  | .exited s => writeU32 s
  | .detachAll | .kill | .info | .history | .wait | .labelClear | .done => []
  | .unknown _ p => p

/-- Interpret one frame. Total: every (tag, payload) is some `Msg`.
An if-chain rather than a literal match so fall-through to `unknown`
is provable by `t ≠ 0, …, t ≠ 15` instead of match-compilation facts. -/
def decodeMsg (tag : UInt8) (p : List UInt8) : Msg :=
  if tag = 0 then .input p
  else if tag = 1 then .output p
  else if tag = 2 then .resize (readU32 p) (readU32 (p.drop 4))
  else if tag = 3 then .attach (readU32 p) (readU32 (p.drop 4))
  else if tag = 4 then .detachAll
  else if tag = 5 then .kill
  else if tag = 6 then .info
  else if tag = 7 then .infoReply p
  else if tag = 8 then .history
  else if tag = 9 then .exited (readU32 p)
  else if tag = 10 then .wait
  else if tag = 11 then .labelSet p
  else if tag = 12 then .labelUnset p
  else if tag = 13 then .labelClear
  else if tag = 14 then .done
  else if tag = 15 then .err p
  else .unknown tag p

/-- A message the encoder may legally emit: payload within §Bound, and
`unknown` only for genuinely unassigned tags (an `unknown` wearing a
known tag would decode as the known message — nothing may build one). -/
def Msg.wf (m : Msg) : Prop :=
  m.payload.length ≤ maxPayload ∧
  match m with
  | .unknown t _ => knownTag t = false
  | _ => True

/-- One frame: tag byte, LE length, payload. -/
def encode (m : Msg) : List UInt8 :=
  m.tag :: writeU32 (UInt32.ofNat m.payload.length) ++ m.payload

/-! ## Incremental decoder -/

/-- Decoder state. `errored` is sticky: an oversize frame poisons the
connection (the runtime closes it) instead of buffering unboundedly. -/
structure Decoder where
  buf : List UInt8 := []
  errored : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Greedily peel complete frames off `bytes`. Returns
(remaining-partial-bytes, errored, messages in arrival order). -/
def takeFrames (bytes : List UInt8) : List UInt8 × Bool × List Msg :=
  match bytes with
  | t :: l0 :: l1 :: l2 :: l3 :: rest =>
    let len := (readU32 [l0, l1, l2, l3]).toNat
    if len > maxPayload then
      ([], true, [])
    else if rest.length < len then
      (bytes, false, [])
    else
      let (buf, err, msgs) := takeFrames (rest.drop len)
      (buf, err, decodeMsg t (rest.take len) :: msgs)
  | _ => (bytes, false, [])
termination_by bytes.length
decreasing_by simp; omega

/-- Feed a chunk. Emits every message completed by it. No-op once errored. -/
def Decoder.feed (d : Decoder) (chunk : List UInt8) : Decoder × List Msg :=
  if d.errored then (d, [])
  else
    let (buf, err, msgs) := takeFrames (d.buf ++ chunk)
    ({ buf, errored := err }, msgs)

/-- Decode a whole stream from scratch (specification form of `feed`). -/
def decode (bytes : List UInt8) : Decoder × List Msg :=
  Decoder.feed {} bytes

/-- Feed many chunks in sequence, concatenating the decoded messages —
the specification of the runtime's read loop (each poll round feeds one
chunk). Structural recursion rather than a `foldl` so the §Stream
induction steps through it directly. -/
def Decoder.feedAll (d : Decoder) : List (List UInt8) → Decoder × List Msg
  | [] => (d, [])
  | c :: cs =>
    let r := d.feed c
    let rest := r.1.feedAll cs
    (rest.1, r.2 ++ rest.2)

end Linger.Core.Wire
