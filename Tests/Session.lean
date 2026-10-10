module

import all Linger.Core.Session
-- These fixtures read the screen they assert about and run compiled under `native_decide`.
import all Linger.Core.Vt
meta import Linger.Core.Session

/-! # Session state-machine scenario tests

Whole client conversations at the pure level: events in, effects out —
no sockets involved. Frames are built with the real `Wire.encode`, so
these also exercise the per-client decoder path the daemon runs.

**Friend module** (lean-modules Step 5): the fixtures that rig rosters and
scanners directly (`{ s0 with clients := …, scan := … }`) are legitimate test
scaffolding, and `import all Linger.Core.Session` is what admits it now that
the daemon itself cannot do the same. -/

namespace Linger.Core.Session.Tests

open Linger.Core.Terminal
open Linger.Core.Wire (Msg encode)

def s0 : State := { vt := Vt.Vt.init 20 5, metaKv := [("name", "t")] }

/-- Run a list of events, collecting effects — the Core `run` (so every
scenario below concretely pins its state threading + effect order),
with the test-friendly argument order. -/
def run (evs : List Event) (s : State := s0) : State × List Effect := Linger.Core.Session.run s evs

/-- Attach: client connects, sends attach frame, gets a restore
(output frames) and the pty is resized. -/
example :
    (let (s, effs) := run [.connected 1, .bytes 1 (encode (.attach 100 30))]
     (s.client? 1).any (·.attached)
       && effs.any (fun e => match e with | .resizePty 100 30 => true | _ => false)
       && effs.any (fun e => match e with | .replay 1 _ => true | _ => false)
       && s.vt.cols == 100 && s.vt.rows == 30) = true := by native_decide

/-- Keystrokes are forwarded to the pty verbatim, not interpreted. -/
example :
    (let (_, effs) :=
        run [.connected 1, .bytes 1 (encode (.attach 80 24)), .bytes 1 (encode (.input [104, 105]))]
     effs.any
        (fun e =>
          match e with
          | .writePty [104, 105] => true
          | _ => false)) =
      true := by
  native_decide

/-- pty output reaches the emulator AND every attached client — but a
detached session still advances (§Detach, executable form). -/
example :
    (let (s1, effs1) := run [.connected 1, .bytes 1 (encode (.attach 80 24)),
                             .ptyOut "hello".toUTF8.toList]
     let (s2, effs2) := run [.ptyOut "hello".toUTF8.toList]
     effs1.any (fun e => match e with | .send 1 (.output _) => true | _ => false)
       && !effs2.any (fun e => match e with | .send _ _ => true | _ => false)
       && ((s1.vt.getRow 0).toList.take 5 == (s2.vt.getRow 0).toList.take 5)) = true := by
  native_decide

def ptyWrites (effs : List Effect) : List (List UInt8) :=
  effs.filterMap
    (fun e =>
      match e with
      | .writePty bs => some bs
      | _ => none)

/-- DA1 is owned once with zero, one, or two clients: the reply stream is
identical and no presentation output frame leaks the request. -/
example :
    (let query := [ESC, 0x5B, 0x63]
     let one : State := { s0 with clients := [{ id := 1, attached := true }] }
      let two : State :=
        { s0 with clients := [{ id := 1, attached := true }, { id := 2, attached := true }] }
      let rz := step s0 (.ptyOut query)
      let r1 := step one (.ptyOut query)
      let r2 := step two (.ptyOut query)
      ptyWrites rz.2 == [da1Reply] && ptyWrites r1.2 == [da1Reply] &&
        ptyWrites r2.2 == [da1Reply] &&
        !r1.2.any
            (fun e =>
              match e with
              | .send _ (.output _) => true
              | _ => false) &&
        !r2.2.any
            (fun e =>
              match e with
              | .send _ (.output _) => true
              | _ => false)) =
      true := by
  native_decide

/-- A query split across pty reads persists in the sole scanner and replies
once when its final byte arrives. -/
example :
    (let first := step s0 (.ptyOut [ESC, 0x5B])
     let second := step first.1 (.ptyOut [0x63])
     first.2.isEmpty && ptyWrites second.2 == [da1Reply] &&
       second.1.scan == .ground) = true := by
  native_decide

/-- Child exit flushes an incomplete prefix before exited/close effects and
resets the scanner without feeding those bytes to `Vt` again. -/
example :
    (let s : State := { s0 with scan := .csi [0x5B, ESC],
                                clients := [{ id := 7, attached := true }] }
     let r := step s (.childExited 0)
     r.1.scan == .ground && r.1.vt.cursor == s.vt.cursor &&
       r.2 == [.send 7 (.output [ESC, 0x5B]), .send 7 (.exited 0), .close 7,
               .dropCheckpoint, .exit]) = true := by
  native_decide

/-- A client closing changes nothing but the roster (a checkpoint
effect is permitted — that's the reboot-resume save point). -/
example :
    (let (sA, _) := run [.connected 1, .bytes 1 (encode (.attach 80 24)),
                         .ptyOut "x".toUTF8.toList]
     let (sB, effsB) := step sA (.closed 1)
     sB.clients.isEmpty && effsB.all (· == .checkpoint)
       && (sB.vt.getRow 0 == sA.vt.getRow 0)) = true := by native_decide

/-- info replies with meta and labels; labels round-trip. -/
example :
    (let (_, effs) :=
        run
          [.connected 1, .bytes 1 (encode (.labelSet "env=dev".toUTF8.toList)),
            .bytes 1 (encode .info)]
     effs.any
        (fun e =>
          match e with
          | .send 1 (.infoReply bs) =>
            let txt := String.fromUTF8? (ByteArray.mk bs.toArray) |>.getD ""
            txt.contains "label.env\tdev"
          | _ => false)) =
      true := by
  native_decide

/-- A C1 control in a label (U+009B, the 8-bit CSI) reaches `infoText` as U+FFFD, the
bytes 239 191 189: `info`, `get` and `ls --porcelain` print these records. -/
example :
    (let (s, _) := run [.connected 1, .bytes 1 (encode (.labelSet "k=a\u009b31mb".toUTF8.toList))]
     let txt := String.fromUTF8? (ByteArray.mk (infoText s).toArray) |>.getD ""
     txt.contains "label.k\ta\uFFFD31mb" && !txt.contains '\u009b') =
      true := by
  native_decide

/-- Each label fits an incoming wire frame; their combined info need not. -/
def largeInfoLabels (count : Nat) : List (String × String) :=
  let value := String.ofList (List.replicate (Wire.maxPayload / 2) 'x')
  (List.range count).map (fun i => (toString i, value))

def storeInfoLabels (labels : List (String × String)) : State × List Effect :=
  run
    (.connected 1 ::
      labels.map (fun (k, v) => .bytes 1 (encode (.labelSet s!"{k}={v}".toUTF8.toList))))
    (State.boot (Vt.Vt.init 20 5) [] [("name", "t")])

def infoReplies (effs : List Effect) : List Msg :=
  effs.filterMap
    (fun e =>
      match e with
      | .send 1 m => some m
      | _ => none)

/-- Two legal labels used to produce one illegal outgoing frame. The real
wire decoder must accept the entire reply, including every byte of both labels. -/
example :
    (let labels := largeInfoLabels 2
     let (s, acks) := storeInfoLabels labels
      let (after, effs) := step s (.bytes 1 (encode .info))
      let msgs := infoReplies effs
      let (dec, received) := Wire.decode (msgs.flatMap encode)
      labels.all (fun (k, v) => s!"{k}={v}".toUTF8.size ≤ Wire.maxPayload) && s.labels == labels &&
        acks == List.replicate labels.length (.send 1 .done) &&
        after.labels == labels &&
        Wire.maxPayload < (infoText s).length &&
        (infoText s).length < infoReplyCap &&
        msgs.length > 2 &&
        msgs.all (fun m => m.payload.length ≤ outputChunk) &&
        !dec.errored &&
        dec.buf.isEmpty &&
        received.getLast? == some .done &&
        (received.filterMap
              (fun m =>
                match m with
                | .infoReply bs => some bs
                | _ => none)).flatten ==
          infoText s) =
      true := by
  native_decide

/-- Many independently accepted labels can exceed the whole-answer policy.
Refuse that request without sending a prefix, reporting done, or losing labels. -/
example :
    (let labels := largeInfoLabels 9
     let (s, acks) := storeInfoLabels labels
      let (after, effs) := step s (.bytes 1 (encode .info))
      labels.all (fun (k, v) => s!"{k}={v}".toUTF8.size ≤ Wire.maxPayload) && s.labels == labels &&
        acks == List.replicate labels.length (.send 1 .done) &&
        after.labels == labels &&
        infoReplyCap < (infoText s).length &&
        (match infoReplies effs with
        | [.err bs] =>
          String.fromUTF8? (ByteArray.mk bs.toArray) == some "info reply exceeds the byte limit"
        | _ => false)) =
      true := by
  native_decide

/-- Exactly the byte cap completes; one byte beyond it is refused. -/
example :
    (let atCap := infoMsgs 1 (List.replicate infoReplyCap 0x78)
     let over := infoMsgs 1 (List.replicate (infoReplyCap + 1) 0x78)
     atCap.getLast? == some (.send 1 .done) &&
       (match over with
       | [.send 1 (.err _)] => true
       | _ => false)) =
      true := by
  native_decide

/-- One read earns one reply: of 1,000 `.history` requests decoded from one
chunk, the first is answered and every later one is refused. -/
example :
    (let (_, effs) := run [.connected 1, .bytes 1 (List.replicate 1000 (encode .history)).flatten]
     effs.count (.send 1 .done) == 1 &&
        effs.count (.send 1 (.err "one request per read".toUTF8.toList)) == 999) =
      true := by
  native_decide

/-- The allowance renews with every read, so a client that waits for each reply
is unaffected; within one read, every reply-bearing request shares it. -/
example :
    (let (_, waited) :=
        run
          [.connected 1, .bytes 1 (encode .history), .bytes 1 (encode .screen),
            .bytes 1 (encode .info), .bytes 1 (encode (.resize 30 10))]
     let (s, batched) :=
        run
          [.connected 2,
            .bytes 2 (encode .info ++ encode .history ++ encode .screen ++ encode (.resize 30 10))]
     waited.count (.send 1 .done) == 4 && batched.count (.send 2 .done) == 1 &&
       batched.count (.send 2 (.err "one request per read".toUTF8.toList)) == 3 &&
       s.vt.cols == 20) =
      true := by
  native_decide

/-! ### `detach-all` and label removal (pin-the-gaps items 2 and 3)

`onMsg_detachAll` / `onMsg_labelUnset` / `onMsg_labelClear` pin the effect lists
as equations; these run the same three verbs through the real decoder so the
promise is checked end to end, and they are what fails if an arm is rewired
rather than merely reshaped. -/

/-- **`detach-all` closes the attached clients and spares a control connection.**
Clients 1 and 2 attach; client 3 never does — it is the `linger detach` control
connection, and it is the one asking. The `.attached` filter is the claim: drop it
and client 3 closes its own socket before its `.done` is read. -/
example :
    (let (_, effs) := run [.connected 1, .bytes 1 (encode (.attach 80 24)),
                           .connected 2, .bytes 2 (encode (.attach 80 24)),
                           .connected 3, .bytes 3 (encode .detachAll)]
     effs.contains (.close 1) && effs.contains (.close 2)
       && !effs.contains (.close 3)
       && effs.contains (.send 3 .done)) = true := by native_decide

/-- A close requested by an attached sender stops the rest of its decoded
packet before it can change labels, write input or resize the child. -/
example :
    (let s := (run [.connected 1, .bytes 1 (encode (.attach 20 5))]).1
     let packet :=
        encode .detachAll ++ encode (.labelSet "after=detach".toUTF8.toList) ++
          encode (.input [0x78]) ++
          encode (.resize 21 6)
      let r := step s (.bytes 1 packet)
      r.1.labels.isEmpty && r.1.vt.colCount == 20 && r.1.vt.rowCount == 5 &&
        r.2 == [.close 1, .send 1 .done]) =
      true := by
  native_decide

/-- Detaching someone else does not stop a control connection's next command. -/
example :
    (let s := (run [.connected 1, .bytes 1 (encode (.attach 20 5)), .connected 2]).1
     let r := step s (.bytes 2 (encode .detachAll ++ encode (.labelSet "after=control".toUTF8.toList)))
     r.1.labels == [("after", "control")] &&
       r.2 == [.close 1, .send 2 .done, .send 2 .done]) = true := by
  native_decide

/-- Exit also stops the decoded packet; later input must not follow kill. -/
example :
    (let s := (run [.connected 1]).1
     let packet :=
        encode .kill ++ encode (.labelSet "after=kill".toUTF8.toList) ++ encode (.input [0x78])
      let r := step s (.bytes 1 packet)
      r.1.labels.isEmpty && r.2 == [.killChild, .dropCheckpoint, .exit]) =
      true := by
  native_decide

/-- **`unset` removes exactly the named key**: `env` goes, `role` stays. A whole-
store clear would satisfy "env is gone" too, which is why `role` is here. -/
example :
    (let (s, _) :=
        run
          [.connected 1, .bytes 1 (encode (.labelSet "env=dev".toUTF8.toList)),
            .bytes 1 (encode (.labelSet "role=web".toUTF8.toList)),
            .bytes 1 (encode (.labelUnset "env".toUTF8.toList))]
     s.labels == [("role", "web")]) =
      true := by
  native_decide

/-- **`clear` empties the store.** -/
example :
    (let (s, _) :=
        run
          [.connected 1, .bytes 1 (encode (.labelSet "env=dev".toUTF8.toList)),
            .bytes 1 (encode (.labelSet "role=web".toUTF8.toList)), .bytes 1 (encode .labelClear)]
     s.labels.isEmpty) =
      true := by
  native_decide

/-- Unsetting a key that was never set is a no-op, not an error: the store is
untouched and no `.err` is sent, so `linger unset` is idempotent for a script. -/
example :
    (let (s, effs) :=
        run
          [.connected 1, .bytes 1 (encode (.labelSet "env=dev".toUTF8.toList)),
            .bytes 1 (encode (.labelUnset "nosuch".toUTF8.toList))]
     s.labels == [("env", "dev")] &&
        !effs.any
            (fun e =>
              match e with
              | .send _ (.err _) => true
              | _ => false)) =
      true := by
  native_decide

/-- An unset with an **invalid UTF-8** payload decodes to `""`, which matches no
key `.labelSet` can store (it rejects an empty key) — so the store survives. This
is the branch `onMsg_labelUnset`'s `getD ""` exists for. -/
example :
    (let (s, _) :=
        run
          [.connected 1, .bytes 1 (encode (.labelSet "env=dev".toUTF8.toList)),
            .bytes 1 (encode (.labelUnset [0xFF, 0xFE]))]
     s.labels == [("env", "dev")]) =
      true := by
  native_decide

/-! ### Agent observability fields (specs/archive/agent-cli.md Step 1)

`info` carries what an agent needs to *see* the session: geometry + cursor
(for `capture`), `alt` (a full-screen app is live), and `outseq` (the change
cursor — "look again only when it moved"). Pinned against the record text so a
renamed or dropped key fails here, not in a consumer. -/

def infoTxt (s : State) : String := String.fromUTF8? (ByteArray.mk (infoText s).toArray) |>.getD ""

/-- Geometry and cursor are reported, current as of the reply. -/
example :
    (let (s, _) := run [.ptyOut "hi".toUTF8.toList]
     let txt := infoTxt s
     txt.contains "cols\t20" && txt.contains "rows\t5"
       && txt.contains "cursorx\t2"
       && txt.contains "cursory\t0") = true := by native_decide

/-- `alt` flips with the alt screen (1049h enters, 1049l leaves). -/
example :
    (let (sIn, _) := run [.ptyOut "\x1b[?1049h".toUTF8.toList]
     let (sOut, _) := run [.ptyOut "\x1b[?1049l".toUTF8.toList] sIn
     (infoTxt sIn).contains "alt\ttrue"
       && (infoTxt sOut).contains "alt\tfalse") = true := by native_decide

/-- `outseq` counts pty-output events — the agent's change cursor. -/
example :
    (let (s2, _) := run [.ptyOut "a".toUTF8.toList, .ptyOut "b".toUTF8.toList]
     (infoTxt s2).contains "outseq\t2") =
      true := by
  native_decide

/-! ### capture (specs/archive/agent-cli.md Step 2)

`.screen` replies with the grid — never the ring — and marks the session seen.
The scenario forces the two apart: eight printed lines on a five-row screen
push three into scrollback, so a capture that painted `history` would show
eight lines and start at `line0`. -/

def eightLines : List UInt8 :=
  (String.intercalate "\r\n" ((List.range 8).map (fun i => s!"line{i}"))).toUTF8.toList

example :
    (let (s1, _) := run [.ptyOut eightLines]
     let (s2, effs) := run [.connected 9, .bytes 9 (encode .screen)] s1
      let sent :=
        (effs.filterMap
            (fun e =>
              match e with
              | .send 9 (.output bs) => some bs
              | _ => none)).flatten
      -- the reply is exactly the screen: five lines, the first being line3…
      sent == Render.screenText s1.vt && sent.count 0x0A == 5 &&
        ((String.fromUTF8? (ByteArray.mk sent.toArray)).getD "").startsWith "line3" &&
        effs.any
          (fun e =>
            match e with
            | .send 9 .done => true
            | _ => false)
        -- …while the ring really holds more (non-vacuity: history shows 8)
        && (Render.history s2.vt).count 0x0A == 8
        -- a capture is a look: unread before, read after, nothing behind
        && unseen s1 &&
        !unseen s2 &&
        behind s2 == 0
        -- and the screen itself is untouched by being looked at
        && s2.vt.grid == s1.vt.grid &&
        s2.labels == s1.labels) =
      true := by
  native_decide

/-- `wait` parks until the child exits; a clean exit drops the checkpoint. -/
example :
    (let (_, effs) := run [.connected 1, .bytes 1 (encode .wait),
                           .childExited 0]
     effs.any (fun e => match e with | .send 1 (.exited 0) => true | _ => false)
       && effs.contains .dropCheckpoint
       && effs.contains .exit) = true := by native_decide

/-- An unknown tag in a real frame does nothing at all (§Frame). -/
example :
    (let quiet := run [.connected 1, .bytes 1 (encode (.unknown 99 [1, 2, 3]))]
     let base := run [.connected 1]
     quiet.2 == base.2 && quiet.1.clients.length == base.1.clients.length) = true := by
  native_decide

/-- The 17th client is refused (§Bound: maxClients = 16). -/
example :
    (let evs := (List.range 17).map Event.connected
     let (s, effs) := run evs
     s.clients.length == 16
       && effs.any (fun e => match e with | .close 16 => true | _ => false)
       && effs.any (fun e => match e with | .send 16 (.err _) => true | _ => false))
      = true := by native_decide

/-- A malformed frame (oversize length claim) gets the client dropped,
not buffered (§Bound at the session layer). -/
example :
    (let (s, effs) := run [.connected 1, .bytes 1 [0, 1, 0, 4, 0]]
     s.clients.isEmpty &&
        effs.any
          (fun e =>
            match e with
            | .close 1 => true
            | _ => false)) =
      true := by
  native_decide

/-- Checkpoint cadence: dirty output + a late-enough tick ⇒ exactly one
checkpoint; a second immediate tick does nothing. -/
example :
    (let (s1, e1) := run [.ptyOut "x".toUTF8.toList, .tick 70000]
     let (_, e2) := step s1 (.tick 70001)
     e1.contains .checkpoint && e2.isEmpty) = true := by native_decide

/-- A checkpoint thirty seconds below the UInt64 boundary must not make the
next dirty tick eligible after only one millisecond. -/
example :
    (let (saved, initial) := run [.ptyOut [65], .tick 18446744073709521616]
     let last := saved.lastCkptMs
      let dirty := (step saved (.ptyOut [66])).1
      let (early, effs) := step dirty (.tick (last + 1))
      initial == [.checkpoint] && effs.isEmpty && early.dirty && early.lastCkptMs == last) =
      true := by
  native_decide

/-- At the exact cadence across the UInt64 boundary, save once and advance the
attempt clock without wrapping it into the past. -/
example :
    (let (saved, _) := run [.ptyOut [65], .tick 18446744073709521616]
     let last := saved.lastCkptMs
      let dirty := (step saved (.ptyOut [66])).1
      let (due, effs) := step dirty (.tick (last + ckptIntervalMs))
      effs == [.checkpoint] && !due.dirty && due.lastCkptMs > last &&
        due.lastCkptMs == last + ckptIntervalMs) =
      true := by
  native_decide

/-- A malformed final attacher still reaches the last-detach save point.
The decoder must be removed immediately, before runtime close feedback. -/
example :
    (let (s, _) := run [.connected 1, .bytes 1 (encode (.attach 20 5)), .ptyOut [65]]
     let (s, effs) := step s (.bytes 1 [255, 255, 255, 255, 255])
     s.clients.isEmpty && effs == [.close 1, .checkpoint] &&
       (step s (.closed 1)).2.isEmpty) = true := by
  native_decide

/-- Attach after exit tells the client immediately. -/
example :
    (let (s1, _) := run [.childExited 3]
     let (_, effs) := run [.connected 9, .bytes 9 (encode (.attach 80 24))] s1
     effs.any (fun e => match e with | .send 9 (.exited 3) => true | _ => false))
      = true := by native_decide

/-! ### Observer and size owner

The read-only observer and size-owner rules: an observer mirrors output but never
owns the size, and the newest attached sizer wins. -/

/-- An observer (attach 0×0) sees output but its keys go nowhere. -/
example :
    (let (_, effs) :=
        run
          [.connected 1, .bytes 1 (encode (.attach 0 0)), .bytes 1 (encode (.input [120])),
            .ptyOut [104, 105]]
     (!effs.any
            (fun e =>
              match e with
              | .writePty _ => true
              | _ => false)) &&
        effs.any
          (fun e =>
            match e with
            | .send 1 (.output _) => true
            | _ => false)) =
      true := by
  native_decide

/-- The newest full attacher owns the size; an older client's resize
is recorded but does not touch the pty. -/
example :
    (let (_, effs) := run [
        .connected 1, .bytes 1 (encode (.attach 80 24)),
        .connected 2, .bytes 2 (encode (.attach 100 30)),
        .bytes 1 (encode (.resize 120 40))]
     let resizes := effs.filterMap (fun e => match e with
       | .resizePty c r => some (c, r) | _ => none)
     resizes == [(80, 24), (100, 30)]) = true := by native_decide

/-- A same-size reattach preserves the scroll region and tab ruler the child set:
`Vt.resize` resets `top`/`bot`/`tabs`, so an unconditional resize on attach would
wipe a child's `DECSTBM` and tab stops, and no `SIGWINCH` fires at an unchanged
winsize to make it re-emit them (restore-conformance Step 0 ledger 1). -/
example :
    (let dirty := "\x1b[2;4r\x1b[3g".toUTF8.toList  -- DECSTBM top=1 bot=3, clear all tabs
     let (s, _) := run [.connected 1, .bytes 1 (encode (.attach 20 5)),
                        .ptyOut dirty,
                        .connected 2, .bytes 2 (encode (.attach 20 5))]
     s.vt.top == 1 && s.vt.bot == 3 && s.vt.tabs == Array.replicate 20 false) = true := by
  native_decide

/-- Non-vacuity: a genuine size change still resets the region (it is size-relative),
so the same-size guard is what preserves it above, not a dead resize. -/
example :
    (let dirty := "\x1b[2;4r".toUTF8.toList
     let (s, _) := run [.connected 1, .bytes 1 (encode (.attach 20 5)),
                        .ptyOut dirty,
                        .connected 2, .bytes 2 (encode (.attach 40 10))]
     s.vt.top == 0 && s.vt.bot == 9) = true := by native_decide

/-- An observer never owns the size, even as the newest attacher. -/
example :
    (let (_, effs) := run [
        .connected 1, .bytes 1 (encode (.attach 80 24)),
        .connected 2, .bytes 2 (encode (.attach 0 0)),
        .bytes 2 (encode (.resize 5 5))]
     let resizes := effs.filterMap (fun e => match e with
       | .resizePty c r => some (c, r) | _ => none)
     resizes == [(80, 24)]) = true := by native_decide

/-! ### control resize (specs/archive/agent-cli.md Step 4)

`linger resize` from a non-attached connection: applies to a detached
session, is refused — loudly — while an attached sizer exists, and leaves the
emulator alone at an unchanged size. -/

/-- Every resize path sends the model's effective dimensions, even when a wire
dimension exceeds both the emulator cap and the kernel's winsize field. -/
example :
    ([[Event.connected 1, .bytes 1 (encode (.attach 65536 5))],
            [.connected 1, .bytes 1 (encode (.resize 65536 5))],
            [.connected 1, .bytes 1 (encode (.attach 20 5)),
              .bytes 1 (encode (.resize 65536 5))]].all
        fun evs =>
        let (s, effs) := run evs
        s.vt.colCount == Linger.Core.Vt.clampDim 65536 &&
          (effs.filterMap fun
                | .resizePty c r => some (c.toNat, r.toNat)
                | _ => none).getLast? ==
            some (s.vt.colCount, s.vt.rowCount)) =
      true := by
  native_decide

/-- An attached resize with no effective change preserves the child's scroll
region and tab ruler too, including a repeated oversized request. -/
example :
    ([20, 65536].all fun width =>
        let (s, _) :=
          run
            [.connected 1, .bytes 1 (encode (.attach width 5)),
              .ptyOut "\x1b[2;4r\x1b[3g".toUTF8.toList, .bytes 1 (encode (.resize width 5))]
        s.vt.top == 1 && s.vt.bot == 3 && s.vt.tabs == Array.replicate s.vt.colCount false) =
      true := by
  native_decide

/-- Quiet label edits are persistent changes even without any new pty output. -/
example :
    ([Msg.labelSet "a=new".toUTF8.toList, .labelUnset "a".toUTF8.toList, .labelClear].all fun msg =>
        let s := { s0 with labels := [("a", "old")] }
        let changed := (onMsg s { id := 1 } msg).1
        (step changed (.tick ckptIntervalMs)).2.contains .checkpoint) =
      true := by
  native_decide

/-- A geometry-only change also reaches the periodic save point. -/
example :
    (let (s, _) := run [.connected 1, .bytes 1 (encode (.resize 40 10))]
     (step s (.tick ckptIntervalMs)).2.contains .checkpoint) = true := by
  native_decide

/-- Detached session: the control resize applies (one resizePty, then done)
and the emulator follows. -/
example :
    (let (s, effs) := run [.connected 1, .bytes 1 (encode (.resize 100 30))]
     let resizes := effs.filterMap (fun e => match e with
       | .resizePty c r => some (c, r) | _ => none)
     resizes == [(100, 30)] && s.vt.cols == 100 && s.vt.rows == 30
       && effs.any (fun e => match e with
            | .send 1 .done => true | _ => false)) = true := by native_decide

/-- While a sizer is attached, the control resize is refused with an `.err`,
no `resizePty` is emitted beyond the attach's own, and the emulator keeps the
attached client's size. -/
example :
    (let (s, effs) := run [
        .connected 1, .bytes 1 (encode (.attach 80 24)),
        .connected 2, .bytes 2 (encode (.resize 100 30))]
     let resizes := effs.filterMap (fun e => match e with
       | .resizePty c r => some (c, r) | _ => none)
     resizes == [(80, 24)] && s.vt.cols == 80 && s.vt.rows == 24
       && effs.any (fun e => match e with
            | .send 2 (.err _) => true | _ => false)) = true := by native_decide

/-- …and once the owner leaves, the same request applies: attachment is the
fact that decides, not history. -/
example :
    (let (s, effs) := run [
        .connected 1, .bytes 1 (encode (.attach 80 24)),
        .closed 1,
        .connected 2, .bytes 2 (encode (.resize 100 30))]
     let resizes := effs.filterMap (fun e => match e with
       | .resizePty c r => some (c, r) | _ => none)
     resizes == [(80, 24), (100, 30)] && s.vt.cols == 100) = true := by native_decide

/-- A same-size control resize is a `.done` no-op that preserves what
`Vt.resize` would wipe: the child's scroll region and tab ruler (the attach
guard's reason, applied to this path — restore-conformance Step 0 ledger 1). -/
example :
    (let dirty := "\x1b[2;4r\x1b[3g".toUTF8.toList  -- DECSTBM 2..4, clear all tabs
     let (s, effs) := run [.ptyOut dirty,
                                 .connected 5, .bytes 5 (encode (.resize 20 5))]
     s.vt.top == 1 && s.vt.bot == 3 && s.vt.tabs == Array.replicate 20 false
       && !effs.any (fun e => match e with
            | .resizePty _ _ => true | _ => false)
       && effs.any (fun e => match e with
            | .send 5 .done => true | _ => false)) = true := by native_decide

/-- A zero dimension is never a size (0×0 is the observer marker on attach). -/
example :
    (let (s, effs) := run [.connected 1, .bytes 1 (encode (.resize 0 30))]
     s.vt.cols == 20 &&
        effs.any
          (fun e =>
            match e with
            | .send 1 (.err _) => true
            | _ => false)) =
      true := by
  native_decide

/-- `info` reports the attached-client count (the `ls` row's `+N` marker,
as data). -/
example :
    (let (_, effs) :=
        run [.connected 1, .bytes 1 (encode (.attach 80 24)), .connected 2, .bytes 2 (encode .info)]
     effs.any
        (fun e =>
          match e with
          | .send 2 (.infoReply bs) =>
            let txt := (String.fromUTF8? (ByteArray.mk bs.toArray)).getD ""
            txt.contains "clients\t1"
          | _ => false)) =
      true := by
  native_decide

/-! ### §Row/§Status integrity — the forged listing record

Step 0 ledger item 2 of `specs/archive/restore-conformance.md`, as a fixture. `infoText` frames
records as `k` TAB `v` LF, `.labelSet` applies no filter and `linger set` passes the
value through — so a label value carrying a newline and a tab used to forge an **extra
record**, including a `status`/`state` pair that `linger list` would then display as the
session's state.

`infoText_records` proves it cannot happen now. -/

def forged : State := { s0 with labels := [("x", "a\nstatus\tlive")] }

/-- The injected controls are replaced by U+FFFD, not dropped. -/
example : (infoText forged).any (· == 0xEF) = true := by native_decide

/-- **Boot caps restored labels at `maxLabels`** — the Bounded-at-boot gap,
closed at the door (lean-modules Step 5): `.labelSet` enforces the cap per
message, and a forged checkpoint's 70-label list can no longer boot past it. -/
example :
    (State.boot (Vt.Vt.init 20 5) ((List.range 70).map (fun i => (toString i, "v")))
          []).labels.length ==
      maxLabels := by
  native_decide

end Linger.Core.Session.Tests
