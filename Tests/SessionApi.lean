module

import Linger.Core.Session
import Linger.Core.Buf

/-! Ordinary imports boot and step a session and read its public views, without the
record rewriters that could plant a client the daemon never admitted. Keep this
separate from the friend-import fixtures in `Tests.Session`. -/

open Linger.Core Linger.Core.Session

example (vt : Vt.Vt) : List Effect := (run (State.boot vt [] []) [.connected 0, .tick 0]).2

/-- does not contain `Linger.Core.Session.State.setClient` -/
#guard_msgs (error, substring := true) in
example (s : State) : State := s.setClient { id := 0, decoder := { errored := true } }

/-- does not contain `Linger.Core.Session.State.dropClient` -/
#guard_msgs (error, substring := true) in
example (s : State) : State := s.dropClient 0

/-- Unknown identifier `onMsg` -/
#guard_msgs (error, substring := true) in
#check onMsg

/-- Unknown identifier `feedMsgs` -/
#guard_msgs (error, substring := true) in
#check feedMsgs

/-- Unknown constant `Linger.Core.Buf.Buf.mk` -/
#guard_msgs (error, substring := true) in
#check Buf.Buf.mk

/-- Unknown constant `_private.Linger.Core.Buf.0.Linger.Core.Buf.Buf.bytes` -/
#guard_msgs (error, substring := true) in
#check Buf.Buf.empty.bytes

/-- Unknown constant `Linger.Core.Session.State.mk` -/
#guard_msgs (error, substring := true) in
#check State.mk
