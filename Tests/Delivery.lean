module

public import Linger.Core.Vt
import Linger.Core.Checkpoint
import all Linger.Core.Vt

public section

namespace Linger.Tests.Delivery

open Linger.Core

/-- Alternating truecolour and every attribute force a large, valid two-screen
repaint. Only this test friend constructs the cells; the socket suite receives
an ordinary sealed terminal through checkpoint validation. -/
private def largeScreen (marks : Bool := false) : Vt.Vt :=
  let cols := if marks then 1000 else 400
  let grid :=
    (Array.range 100).map fun _ =>
      (Array.range cols).map fun x =>
        ({ base := 'x', marks := if marks then List.replicate 8 '\u1AB0' else [],
           pen :=
             if marks then {}
             else
               { fg := .rgb (if x % 2 == 0 then 255 else 254) 255 255, bg := .rgb 255 255 255,
                 bold := true, dim := true, italic := true, underline := true, blink := true,
                 reverse := true, strike := true } } :
          Vt.Cell)
  { Vt.Vt.init cols 100 with
    grid, altGrid := some (grid, {}, {}) }

def acceptedScreen (marks : Bool := false) : Option Vt.Vt :=
  (Checkpoint.load (Checkpoint.save { vt := largeScreen marks, cwd := "", labels := [] })).map
    (·.vt)

def acceptedTitle : Option Vt.Vt :=
  let title :=
    String.ofList
      (List.replicate 4095 'α' ++ ['\x1b'] ++ List.replicate 5 '𝄞' ++ ['\n'] ++
        List.replicate 5000 'β')
  let vt := { Vt.Vt.init 20 5 with title }
  (Checkpoint.load (Checkpoint.save { vt, cwd := "", labels := [] })).map (·.vt)

end Linger.Tests.Delivery
