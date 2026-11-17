module

public import Verify.Harness
public import Terminal.CoreSpec
import Terminal.CoreCode.Vt

public section

/-! # Linger.Terminal.Suites.Conform — the emulator against the reference, and against tmux

One fixture of the reference's core sequences, `fixture`, fed through the real emulator as the
daemon feeds a session's output. The emulator must show what the reference model
(`Terminal.Vt.Ref`) computes for it, cell by cell with each cell's pen, with the cursor, the pen
and the title, and it must show what tmux 3.8 showed for the same bytes, captured once with
`tmux capture-pane` on a 10×6 pane: an independent emulator, since no X server on the host runs
xterm. The fixture keeps to what tmux and the reference agree on: it enters no alternate screen
and runs no IL or DL, whose cursor tmux leaves where ECMA-48 moves it to the line home. -/

namespace Linger.Terminal.Suites.Conform

open Verify.Harness
open Terminal.Vt Terminal.Vt.Ref

/-- The fixture: printing with autowrap and a deferred wrap at the right margin, CR, LF, HT, BS,
the cursor movements, ICH, DCH, ECH, EL, ED, SGR with 8, 256 and 24-bit colours, DECSC and DECRC,
DECSTBM with IND and RI inside the region, DECAWM off and on, and an OSC 2 title. -/
def fixture : List Seq :=
  [.print 'h', .print 'i', .cr, .lf, .sgr [.bold, .fg8 1], .print 'X', .sgr [], .ht, .print 'T',
    .cup 3 2, .print 'a', .print 'b', .print 'c', .cub 2, .el 0, .cup 1 9, .print 'w', .print 'r',
    .print 'p', .bs, .print 'Q', .cup 2 4, .ich 2, .print 'Z', .cha 1, .dch 1, .vpa 4, .print 'v',
    .ech 3, .cuf 1, .print 'f', .cuu 1, .print 'u', .cud 5, .print 'd', .decsc, .cup 1 1,
    .sgr [.inverse, .bg256 200, .fgRgb 1 2 3], .print 'R', .decrc, .print 'S', .decstbm 2 4,
    .cup 4 1, .lf, .print 'q', .ri, .ri, .ri, .print 'r', .decstbm 0 0, .cup 6 1, .print 'e', .el 2,
    .print 'E', .cup 5 3, .ed 0, .cup 1 5, .ed 1, .set .wrap false, .cup 2 1, .print '1',
    .print '2', .print '3', .print '4', .print '5', .print '6', .print '7', .print '8', .print '9',
    .print '0', .print '!', .set .wrap true, .ind, .title false "fixture"]

/-- The screen a fresh terminal of this size shows, as the reference holds it: blank, homed, the
default pen and modes, the whole screen as the region and a tab stop every eight columns. -/
def fresh (cols rows : Nat) : Screen :=
  { cols, rows, cell := fun _ _ => {}, x := 0, y := 0, pending := false, pen := {}, modes := {},
    top := 0, bot := rows - 1, tabs := fun i => i % 8 == 0 && i != 0, saved := {}, main := none,
    title := "", bell := false }

/-- What tmux 3.8 showed for the fixture's bytes on a 10×6 pane: its rows, as `capture-pane -p`
printed them padded to the width, the cursor and the title. -/
def tmuxRows :
    List
      String := ["        wr", "123456789!", " a u      ", "v f       ", "          ", "          "]

/-- …the cursor tmux reported, column then row. -/
def tmuxCursor : Nat × Nat := (9, 2)

/-- A row's characters. -/
def rowChars (row : Row) (cols : Nat) : String :=
  String.ofList ((List.range cols).map fun x => (row.getD x default).base)

/-- The checks: the emulator against the reference, cell by cell, and against tmux. -/
def checks : IO Unit := do
  let bytes := fixture.flatMap Seq.bytes
  let v := (Vt.init 10 6).feed bytes
  let r := fixture.foldl Seq.apply (fresh 10 6)
  let cells :=
    (List.range 6).all fun y =>
      (List.range 10).all fun x => (v.getRow y).getD x default == r.cell x y
  expect
      (cells && v.cursorPos == (r.x, r.y) && v.getPen == r.pen && v.getModes == r.modes &&
        v.windowTitle == r.title &&
        v.atBoundary)
      "the emulator shows the reference's cells, pens, cursor, modes and title for the fixture"
  expect
      ((List.range 6).map (fun y => rowChars (v.getRow y) 10) == tmuxRows &&
        v.cursorPos == tmuxCursor &&
        v.windowTitle == "fixture")
      "the emulator shows what tmux 3.8 showed for the fixture's bytes"

end Linger.Terminal.Suites.Conform
