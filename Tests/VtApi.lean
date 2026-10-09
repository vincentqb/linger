module

import Linger.Core.Vt

/-! Ordinary imports expose the checked VT operations, without granting the
raw mutators that can bypass their invariants. Keep this separate from the
friend-import fixtures in `Tests.Vt`. -/

open Linger.Core.Vt

example : Nat := (((Vt.init 2 1).feed [0x61]).step 0x62 |>.resize 3 2 |>.quiesce).colCount

/-- does not contain `Linger.Core.Vt.Vt.putCell` -/
#guard_msgs (error, substring := true) in
#check (Vt.init 2 1).putCell 0 0 { base := '\x1b', width := 1 }

/-- does not contain `Linger.Core.Vt.Vt.printPut` -/
#guard_msgs (error, substring := true) in
#check (Vt.init 2 1).printPut '\x1b' 1

/-- does not contain `Linger.Core.Vt.Vt.printMark` -/
#guard_msgs (error, substring := true) in
#check (Vt.init 2 1).printMark 'x'

/-- does not contain `Linger.Core.Vt.Vt.stepCsi` -/
#guard_msgs (error, substring := true) in
#check (Vt.init 2 1).stepCsi { params := Array.replicate 17 (0, false) } 0x3F

/-- Repr Vt -/
#guard_msgs (error, substring := true) in
#check repr (Vt.init 2 1)
