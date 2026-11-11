module

public import Terminal.Vt
import Linger.Session.Checkpoint
import all Terminal.Vt

public section

namespace Linger.Session.Tests.Delivery

open Terminal

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

/-- `largeScreen marks` as a checkpoint load returns it, or `none` if loading refuses it. -/
def acceptedScreen (marks : Bool := false) : Option Vt.Vt :=
  (Checkpoint.loadBytes
        (Checkpoint.saveBytes { vt := largeScreen marks, cwd := "", labels := [] })).map
    (·.vt)

/-- A small terminal whose title holds an escape, a newline and 9,100 multibyte characters, as a
checkpoint load returns it. -/
def acceptedTitle : Option Vt.Vt :=
  let title :=
    String.ofList
      (List.replicate 4095 'α' ++ ['\x1b'] ++ List.replicate 5 '𝄞' ++ ['\n'] ++
        List.replicate 5000 'β')
  let vt := { Vt.Vt.init 20 5 with title }
  (Checkpoint.loadBytes (Checkpoint.saveBytes { vt, cwd := "", labels := [] })).map (·.vt)

end Linger.Session.Tests.Delivery
