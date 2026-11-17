module

public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Checkpoint
-- A friend import: the handoff carries every field of the sealed `State`, so it reads them all and
-- builds the state its new image resumes from out of what it decoded. It assigns no `Vt` field:
-- the terminal goes through the checkpoint codec, whose decoder validates it.
import all Linger.Session.CoreCode

public section

/-! # Linger.Session.Handoff — the session a daemon hands the image that replaces it

A daemon that upgrades replaces its own image with a newer linger's, by `execve`, which keeps
its process, its program and its descriptors (the world claim `Os.Exec.Keeps`). The new image
resumes from the handoff: the session's whole state and the descriptors and bytes the daemon
kept for it (`World`), so the session goes on where the old image left it, carried rather than
rebuilt. The terminal goes through the checkpoint codec, which keeps every field the emulator
keeps but its partial parser state, so a daemon hands its session over only while its parser is
quiet (`Vt.quiet`); every other field is written here, and the round trip is exact
(`decode_encode`). A handoff begins with its format (`Handoff.header`): a binary decodes the
formats it lists (`Handoff.formats`) and refuses any other (`decode_unknown`), and a daemon hands
its session only to a binary whose probe lists the format it writes (`Upgrade.proceeds`). -/

namespace Linger.Session.Handoff

open Terminal
open Linger.Session.Checkpoint

/-- One byte as itself. -/
def wByte (b : UInt8) : List UInt8 := [b]

/-- Inverse of `wByte`. -/
def rByte : R UInt8 := fun l =>
  match l with
  | [] => none
  | b :: rest => some (b, rest)

/-- Bytes as their count, then each. -/
def wBytes (bs : List UInt8) : List UInt8 := wList wByte bs

/-- Inverse of `wBytes`. -/
def rBytes : R (List UInt8) := fun l => rList rByte l

/-- A 32-bit number as a `Nat`. -/
def wU32 (n : UInt32) : List UInt8 := wNat n.toNat

/-- Inverse of `wU32`. -/
def rU32 : R UInt32 := fun l => do
  let (n, rest) ← rNat l
  some (UInt32.ofNat n, rest)

/-- How a program ended: its kind, then its code or signal. -/
def wOutcome : Outcome → List UInt8
  | .exited code => [0, code]
  | .signaled signal => [1, signal]
  | .unknown => [2]

/-- Inverse of `wOutcome`. -/
def rOutcome : R Outcome := fun l =>
  match l with
  | 0 :: code :: rest => some (.exited code, rest)
  | 1 :: signal :: rest => some (.signaled signal, rest)
  | 2 :: rest => some (.unknown, rest)
  | _ => none

/-- How a session ended: its kind, then the program's ending or the signal; 2 alone for a dismissed
tmux pane, which no daemon carries. -/
def wEnding : Ending → List UInt8
  | .program outcome => 0 :: wOutcome outcome
  | .saved signal => [1, signal]
  | .dismissed => [2]

/-- Inverse of `wEnding`. -/
def rEnding : R Ending := fun l =>
  match l with
  | 0 :: rest => (rOutcome rest).map fun (o, rest) => (.program o, rest)
  | 1 :: signal :: rest => some (.saved signal, rest)
  | 2 :: rest => some (.dismissed, rest)
  | _ => none

/-- A client's mode, as the wire writes it: 0 writable, 1 read-only. -/
def wMode : Mode → List UInt8
  | .writable => [0]
  | .readOnly => [1]

/-- Inverse of `wMode`. -/
def rMode : R Mode := fun l =>
  match l with
  | 0 :: rest => some (.writable, rest)
  | 1 :: rest => some (.readOnly, rest)
  | _ => none

/-- A decoder's incomplete frame and whether it errored. -/
def wDecoder (d : Wire.Decoder) : List UInt8 := wBytes d.buf ++ wBool d.errored

/-- Inverse of `wDecoder`. -/
def rDecoder : R Wire.Decoder := fun l => do
  let (buf, l) ← rBytes l
  let (errored, l) ← rBool l
  some ({ buf, errored }, l)

/-- A client's record, field by field. -/
def wClient (c : Client) : List UInt8 :=
  wNat c.id ++ wU32 c.cols ++ wU32 c.rows ++ wBool c.attached ++ wMode c.mode ++ wNat c.seq ++
    wBool c.waiting ++
    wBool c.answered ++
    wDecoder c.decoder

/-- Inverse of `wClient`. -/
def rClient : R Client := fun l => do
  let (id, l) ← rNat l
  let (cols, l) ← rU32 l
  let (rows, l) ← rU32 l
  let (attached, l) ← rBool l
  let (mode, l) ← rMode l
  let (seq, l) ← rNat l
  let (waiting, l) ← rBool l
  let (answered, l) ← rBool l
  let (decoder, l) ← rDecoder l
  some ({ id, cols, rows, attached, mode, seq, waiting, answered, decoder }, l)

/-- The mediator's scanner: its kind, then what it holds. -/
def wScan : Mediation.Scan → List UInt8
  | .ground => [0]
  | .esc => [1]
  | .csi rev => 2 :: wBytes rev
  | .csiPass => [3]
  | .osc rev escSeen => 4 :: (wBytes rev ++ wBool escSeen)
  | .oscPass escSeen => 5 :: wBool escSeen
  | .dcsIntro => [6]
  | .dcsKind kind => [7, kind]
  | .dcs kind payloadRev escSeen => 8 :: kind :: (wBytes payloadRev ++ wBool escSeen)
  | .strPass escSeen => 9 :: wBool escSeen

/-- Inverse of `wScan`. -/
def rScan : R Mediation.Scan := fun l =>
  match l with
  | 0 :: rest => some (.ground, rest)
  | 1 :: rest => some (.esc, rest)
  | 2 :: rest => (rBytes rest).map fun (rev, rest) => (.csi rev, rest)
  | 3 :: rest => some (.csiPass, rest)
  | 4 :: rest => do
    let (rev, rest) ← rBytes rest
    let (escSeen, rest) ← rBool rest
    some (.osc rev escSeen, rest)
  | 5 :: rest => (rBool rest).map fun (escSeen, rest) => (.oscPass escSeen, rest)
  | 6 :: rest => some (.dcsIntro, rest)
  | 7 :: kind :: rest => some (.dcsKind kind, rest)
  | 8 :: kind :: rest => do
    let (payloadRev, rest) ← rBytes rest
    let (escSeen, rest) ← rBool rest
    some (.dcs kind payloadRev escSeen, rest)
  | 9 :: rest => (rBool rest).map fun (escSeen, rest) => (.strPass escSeen, rest)
  | _ => none

/-- A command line as the mediator read it. -/
def wCmdline (c : Mediation.Cmdline) : List UInt8 := wBytes c.bytes ++ wBool c.whole

/-- Inverse of `wCmdline`. -/
def rCmdline : R Mediation.Cmdline := fun l => do
  let (bytes, l) ← rBytes l
  let (whole, l) ← rBool l
  some ({ bytes, whole }, l)

/-- The ending of a shell's command. -/
def wFinished (f : Finished) : List UInt8 := wCmdline f.cmdline ++ wOpt wNat f.status

/-- Inverse of `wFinished`. -/
def rFinished : R Finished := fun l => do
  let (cmdline, l) ← rCmdline l
  let (status, l) ← rOpt rNat l
  some ({ cmdline, status }, l)

/-- A terminal's foreground, as the operating system reported it. -/
def wForeground (f : Foreground) : List UInt8 := wNat f.pid ++ wList wStr f.argv ++ wStr f.dir

/-- Inverse of `wForeground`. -/
def rForeground : R Foreground := fun l => do
  let (pid, l) ← rNat l
  let (argv, l) ← rList rStr l
  let (dir, l) ← rStr l
  some ({ pid, argv, dir }, l)

/-- What the daemon last read of the world. -/
def wObservation (o : Observation) : List UInt8 :=
  wNat o.nowMs ++ wNat o.wallS ++ wBool o.login ++ wOpt wForeground o.foreground

/-- Inverse of `wObservation`. -/
def rObservation : R Observation := fun l => do
  let (nowMs, l) ← rNat l
  let (wallS, l) ← rNat l
  let (login, l) ← rBool l
  let (foreground, l) ← rOpt rForeground l
  some ({ nowMs, wallS, login, foreground }, l)

/-- The record's fields or the metadata of a session, as a checkpoint writes its fields. -/
def wFields (kvs : List (String × String)) : List UInt8 := wList (wPair wStr wStr) kvs

/-- Inverse of `wFields`. -/
def rFields : R (List (String × String)) := fun l => rList (rPair rStr rStr) l

/-- The terminal, as the session's checkpoint with no directory and no fields, whose codec keeps
every field of the emulator but the partial parser state. -/
def wTerminal (vt : Vt.Vt) : List UInt8 :=
  wBytes (Checkpoint.saveBytes { vt, cwd := "", fields := [] }).data.toList

/-- Inverse of `wTerminal` for a terminal whose parser is quiet (`rTerminal_wTerminal`). -/
def rTerminal : R Vt.Vt := fun l => do
  let (blob, l) ← rBytes l
  let c ← Checkpoint.loadBytes ⟨blob.toArray⟩
  some (c.vt, l)

/-- The session's state, every field in the order the state declares them. -/
def wState (s : State) : List UInt8 :=
  wTerminal s.vt ++ wScan s.scan ++ wList wClient s.clients ++ wFields s.fields ++
    wFields s.metaKv ++
    wOpt wEnding s.ended ++
    wBool s.dirty ++
    wNat s.lastCkptMs ++
    wNat s.attachSeq ++
    wNat s.outSeq ++
    wNat s.lookSeq ++
    wBool s.asking ++
    wOpt wBytes s.notice ++
    wOpt wCmdline s.running ++
    wOpt wFinished s.finished ++
    wNat s.tickOutSeq ++
    wBool s.freshFlag ++
    wOpt wNat s.lastOutMs ++
    wOpt wObservation s.observed

/-- Inverse of `wState` for a state whose terminal's parser is quiet. -/
def rState : R State := fun l => do
  let (vt, l) ← rTerminal l
  let (scan, l) ← rScan l
  let (clients, l) ← rList rClient l
  let (fields, l) ← rFields l
  let (metaKv, l) ← rFields l
  let (ended, l) ← rOpt rEnding l
  let (dirty, l) ← rBool l
  let (lastCkptMs, l) ← rNat l
  let (attachSeq, l) ← rNat l
  let (outSeq, l) ← rNat l
  let (lookSeq, l) ← rNat l
  let (asking, l) ← rBool l
  let (notice, l) ← rOpt rBytes l
  let (running, l) ← rOpt rCmdline l
  let (finished, l) ← rOpt rFinished l
  let (tickOutSeq, l) ← rNat l
  let (freshFlag, l) ← rBool l
  let (lastOutMs, l) ← rOpt rNat l
  let (observed, l) ← rOpt rObservation l
  some
    ({ vt, scan, clients, fields, metaKv, ended, dirty, lastCkptMs, attachSeq, outSeq, lookSeq,
        asking, notice, running, finished, tickOutSeq, freshFlag, lastOutMs, observed },
      l)

/-- One connection a daemon hands over. -/
def wConn (c : Conn) : List UInt8 := wNat c.fd ++ wBytes c.owed ++ wOpt wNat c.closeBy

/-- Inverse of `wConn`. -/
def rConn : R Conn := fun l => do
  let (fd, l) ← rNat l
  let (owed, l) ← rBytes l
  let (closeBy, l) ← rOpt rNat l
  some ({ fd, owed, closeBy }, l)

/-- What the daemon hands over beside the state, field by field. -/
def wWorld (w : World) : List UInt8 :=
  wNat w.listenFd ++ wNat w.ptyFd ++ wNat w.childPid ++ wPair wNat wNat w.signals ++
    wList wNat w.locks ++
    wList wConn w.conns ++
    wBytes w.ptyIn ++
    wBool w.login ++
    wNat w.asker

/-- Inverse of `wWorld`. -/
def rWorld : R World := fun l => do
  let (listenFd, l) ← rNat l
  let (ptyFd, l) ← rNat l
  let (childPid, l) ← rNat l
  let (signals, l) ← rPair rNat rNat l
  let (locks, l) ← rList rNat l
  let (conns, l) ← rList rConn l
  let (ptyIn, l) ← rBytes l
  let (login, l) ← rBool l
  let (asker, l) ← rNat l
  some ({ listenFd, ptyFd, childPid, signals, locks, conns, ptyIn, login, asker }, l)

/-- The handoff of a session: the header of the format this version writes, the state, then what
the daemon kept for it. -/
def encode (s : State) (w : World) : List UInt8 := header version ++ wState s ++ wWorld w

/-- The format a handoff names, when it begins with `magic` and names one this version reads,
and what follows its header. -/
def stripHeader (l : List UInt8) : Option (Nat × List UInt8) :=
  match l with
  | a :: b :: c :: d :: v :: rest =>
    if [a, b, c, d] = magic ∧ formats.contains v.toNat then some (v.toNat, rest) else none
  | _ => none

/-- The session and what the daemon kept for it, from a handoff of a format this version reads:
`none` for one of another format, one cut short, or one with bytes after its end. -/
def decode (l : List UInt8) : Option (State × World) := do
  let (_, l) ← stripHeader l
  let (s, l) ← rState l
  let (w, l) ← rWorld l
  if l.isEmpty then
    some (s, w)
  else
    none

/-- The descriptors an upgrade's exec keeps open for the new image: the listening socket, the pty,
both ends of the signal pipe, the locks and every connection, each one the handoff names
(`upgrade_keeps`). -/
def kept (w : World) : List Nat :=
  [w.listenFd, w.ptyFd, w.signals.1, w.signals.2] ++ w.locks ++ w.conns.map (·.fd)

end Linger.Session.Handoff

namespace Linger.Session.Upgrade

/-- Whether a daemon hands its session to a binary whose probe reported `reported`, the formats
it reads, `none` when it gave no such answer: exactly when it reads the format this version
writes (`proceeds_iff`). -/
def proceeds (reported : Option (List Nat)) : Bool := reported.any (·.contains Handoff.version)

/-- What a binary's probe prints: the formats it reads, in order, separated by spaces. -/
def formatsText : String := " ".intercalate (Handoff.formats.map toString)

/-- The formats a probe printed: its words, each a number, or `none` for an answer with no word
or another word. -/
def readFormats (text : String) : Option (List Nat) :=
  let words := (text.split Char.isWhitespace).toStringList.filter (!·.isEmpty)
  if words.isEmpty then none else words.mapM String.toNat?

end Linger.Session.Upgrade
