module

import Linger.Session.Checkpoint

/-! Ordinary imports write and read checkpoints through `saveBytes` and `loadBytes` and see
`Ckpt` and `magic`. The list codec and the readers stay private to the codec and its
`import all` friends, which is what keeps every runtime decode on the byte-array path. -/

open Linger.Session.Checkpoint

example (c : Ckpt) : Option Ckpt := loadBytes (saveBytes c)

example : List UInt8 := magic

/-- Unknown identifier `Linger.Session.Checkpoint.load` -/
#guard_msgs (error, substring := true) in
#check Linger.Session.Checkpoint.load

/-- Unknown identifier `Linger.Session.Checkpoint.save` -/
#guard_msgs (error, substring := true) in
#check Linger.Session.Checkpoint.save

/-- Unknown identifier `Linger.Session.Checkpoint.rVtB` -/
#guard_msgs (error, substring := true) in
#check Linger.Session.Checkpoint.rVtB
