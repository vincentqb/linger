module

import Linger.Session
import Linger.Session.Buf

/-! Ordinary imports boot and step a session and read its public views, without the
record rewriters that could plant a client the daemon never admitted. Keep this
separate from the friend-import fixtures in `Linger.Session.Tests.Session`. -/

open Linger Linger.Session Terminal
open Terminal.Replay (Plan)

example (vt : Vt.Vt) : List (Effect Plan) := (run (State.boot vt [] []) [.connected 0, .tick 0]).2

-- The roster and the scanner are public-read, for the session bounds; writing either needs the
-- private constructor.
example (s : State) : List Client × Mediation.Scan := (s.clients, s.scan)

-- The observations the headline theorems name.
example (s : State) : Vt.Vt × List Client × List (String × String) × Mediation.Scan :=
  (s.terminal, s.roster, s.labelList, s.scanner)

/-- constructor for `StateRec` is marked as private -/
#guard_msgs (error, substring := true) in
example (s : State) : State := { s with clients := [] }

/-- does not contain `Linger.Session.StateRec.setClient` -/
#guard_msgs (error, substring := true) in
example (s : State) : State := s.setClient { id := 0, decoder := { errored := true } }

/-- does not contain `Linger.Session.StateRec.dropClient` -/
#guard_msgs (error, substring := true) in
example (s : State) : State := s.dropClient 0

/-- Unknown identifier `onMsg` -/
#guard_msgs (error, substring := true) in
#check onMsg

/-- Unknown identifier `feedMsgs` -/
#guard_msgs (error, substring := true) in
#check feedMsgs

/-- Unknown constant `Linger.Session.Buf.BufRec.mk` -/
#guard_msgs (error, substring := true) in
#check Buf.BufRec.mk

/-- Unknown constant `_private.Linger.Session.Buf.0.Linger.Session.Buf.BufRec.bytes` -/
#guard_msgs (error, substring := true) in
#check Buf.Buf.empty.bytes

/-- Unknown constant `Linger.Session.StateRec.mk` -/
#guard_msgs (error, substring := true) in
#check StateRec.mk
