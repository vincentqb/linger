import Zmx.Core.Session
/-! # Session state-machine scenario tests

Whole client conversations at the pure level: events in, effects out —
no sockets involved. Frames are built with the real `Wire.encode`, so
these also exercise the per-client decoder path the daemon runs.
-/

namespace Zmx.Core.Session.Tests

open Zmx.Core.Session
open Zmx.Core.Wire (Msg encode)

def s0 : State := { vt := Vt.Vt.init 20 5, metaKv := [("name", "t")] }

/-- Run a list of events, collecting effects. -/
def run (evs : List Event) (s : State := s0) : State × List Effect :=
  evs.foldl (fun (acc : State × List Effect) ev =>
    let (s', effs) := step acc.1 ev
    (s', acc.2 ++ effs)) (s, [])

def hasEffect (effs : List Effect) (p : Effect → Bool) : Bool := effs.any p

/-- Attach: client connects, sends attach frame, gets a restore
(output frames) and the pty is resized. -/
example :
    (let (s, effs) := run [.connected 1, .bytes 1 (encode (.attach 100 30))]
     (s.client? 1).any (·.attached)
       && hasEffect effs (fun e => match e with | .resizePty 100 30 => true | _ => false)
       && hasEffect effs (fun e => match e with | .send 1 (.output _) => true | _ => false)
       && s.vt.cols == 100 && s.vt.rows == 30) = true := by native_decide

/-- Keystrokes are forwarded to the pty verbatim, not interpreted. -/
example :
    (let (_, effs) := run [.connected 1, .bytes 1 (encode (.attach 80 24)),
                           .bytes 1 (encode (.input [104, 105]))]
     hasEffect effs (fun e => match e with
       | .writePty [104, 105] => true | _ => false)) = true := by native_decide

/-- pty output reaches the emulator AND every attached client — but a
detached session still advances (§Detach, executable form). -/
example :
    (let (s1, effs1) := run [.connected 1, .bytes 1 (encode (.attach 80 24)),
                             .ptyOut "hello".toUTF8.toList]
     let (s2, effs2) := run [.ptyOut "hello".toUTF8.toList]
     hasEffect effs1 (fun e => match e with | .send 1 (.output _) => true | _ => false)
       && !hasEffect effs2 (fun e => match e with | .send _ _ => true | _ => false)
       && ((s1.vt.getRow 0).toList.take 5 == (s2.vt.getRow 0).toList.take 5)) = true := by
  native_decide

/-- A client closing changes nothing but the roster. -/
example :
    (let (sA, _) := run [.connected 1, .bytes 1 (encode (.attach 80 24)),
                         .ptyOut "x".toUTF8.toList]
     let (sB, effsB) := step sA (.closed 1)
     sB.clients.isEmpty && effsB.isEmpty
       && (sB.vt.getRow 0 == sA.vt.getRow 0)) = true := by native_decide

/-- kill: child killed, checkpoint dropped, daemon exits. -/
example :
    (let (_, effs) := run [.connected 1, .bytes 1 (encode .kill)]
     effs.take 3 == [.killChild, .dropCheckpoint, .exit]
       || (hasEffect effs (· == .killChild) && hasEffect effs (· == .exit)
             && hasEffect effs (· == .dropCheckpoint))) = true := by native_decide

/-- info replies with meta and labels; labels round-trip. -/
example :
    (let (_, effs) := run [.connected 1,
                           .bytes 1 (encode (.labelSet "env=dev".toUTF8.toList)),
                           .bytes 1 (encode .info)]
     hasEffect effs (fun e => match e with
       | .send 1 (.infoReply bs) =>
         let txt := String.fromUTF8? (ByteArray.mk bs.toArray) |>.getD ""
         (txt.splitOn "label.env\tdev").length ≥ 2
       | _ => false)) = true := by native_decide

/-- wait parks until the child exits, then everyone is told + closed
and the daemon exits WITHOUT dropping the checkpoint... no — a clean
child exit does drop it (resume is for crashes, not completed work). -/
example :
    (let (_, effs) := run [.connected 1, .bytes 1 (encode .wait),
                           .childExited 0]
     hasEffect effs (fun e => match e with | .send 1 (.exited 0) => true | _ => false)
       && hasEffect effs (· == .dropCheckpoint)
       && hasEffect effs (· == .exit)) = true := by native_decide

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
       && hasEffect effs (fun e => match e with | .close 16 => true | _ => false)
       && hasEffect effs (fun e => match e with | .send 16 (.err _) => true | _ => false))
      = true := by native_decide

/-- A malformed frame (oversize length claim) gets the client dropped,
not buffered (§Bound at the session layer). -/
example :
    (let (s, effs) := run [.connected 1, .bytes 1 [0, 1, 0, 4, 0]]
     s.clients.isEmpty
       && hasEffect effs (fun e => match e with | .close 1 => true | _ => false)) = true := by
  native_decide

/-- Checkpoint cadence: dirty output + a late-enough tick ⇒ exactly one
checkpoint; a second immediate tick does nothing. -/
example :
    (let (s1, e1) := run [.ptyOut "x".toUTF8.toList, .tick 70000]
     let (_, e2) := step s1 (.tick 70001)
     hasEffect e1 (· == .checkpoint) && e2.isEmpty) = true := by native_decide

/-- Attach after exit tells the client immediately. -/
example :
    (let (s1, _) := run [.childExited 3]
     let (_, effs) := run [.connected 9, .bytes 9 (encode (.attach 80 24))] s1
     hasEffect effs (fun e => match e with | .send 9 (.exited 3) => true | _ => false))
      = true := by native_decide

end Zmx.Core.Session.Tests
