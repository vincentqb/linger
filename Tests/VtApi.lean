module

import Linger.Core.Vt

/-! Ordinary imports expose the checked VT operations, without granting the
raw mutators that can bypass their invariants. Keep this separate from the
friend-import fixtures in `Tests.Vt`. -/

open Linger.Core.Vt

#check (((Vt.init 2 1).feed [0x61]).step 0x62 |>.resize 3 2 |>.quiesce).colCount

#check_failure (Vt.init 2 1).putCell 0 0 { base := '\x1b', width := 1 }

#check_failure (Vt.init 2 1).printPut '\x1b' 1

#check_failure (Vt.init 2 1).printMark 'x'

#check_failure (Vt.init 2 1).stepCsi { params := Array.replicate 17 (0, false) } 0x3F
