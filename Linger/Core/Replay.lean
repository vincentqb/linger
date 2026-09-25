module

public import Linger.Core.Render
-- Replay is a second consumer of the renderer's sealed snapshot. It shares
-- rows; it never changes a terminal or exposes its representation.
import all Linger.Core.Vt

private instance : Repr String.Slice where
  reprPrec s _ := repr (s.str, s.startInclusive.offset.byteIdx, s.endExclusive.offset.byteIdx)

deriving instance DecidableEq for String.Slice

public section

namespace Linger.Core.Replay

open Linger.Core.Vt

private inductive Part where
  | bytes (value : Render.Bytes)
  | rows (value : List Row) (pen : Pen)
  | text (value : String.Slice)
  deriving Repr, DecidableEq

/-- A captured repaint. The remaining grids share immutable rows with the
terminal at attach time. `pending` holds one stage, row or bounded title chunk;
neither the complete repaint nor an output-effect backlog is stored. -/
structure Plan where
  private parts : List Part
  private pending : Render.Bytes := []
  deriving Repr, DecidableEq

/-- Capture at the pure event point, before later messages can resize or feed
the terminal. Literal stages are renderer control/history bytes; screen paints
remain shared rows and the title remains a shared slice until demanded. -/
def start (v : Vt) : Plan :=
  let header := Render.csiNum 0 0x6D ++ (Render.csiB ++ [0x48])
  let before :=
    Render.prologueAnsi v ++ Render.csiNum 0 0x6D ++ Render.csiNum 2 0x4A ++
      Render.scrollbackAnsi v ++
      header
  let title :=
    Render.regionAnsi v ++ Render.tabsAnsi v ++ Render.savedAnsi v ++ Render.savedPendingAnsi v ++
      Render.escB ++
      [0x5D, 0x32, 0x3B]
  let after :=
    [0x07] ++ Render.modesAnsi v ++ Render.charsetAnsi v ++ Render.penSgr v.pen ++
      Render.cursorAnsi v ++
      Render.cursorPendingAnsi v
  let screens :=
    match v.altGrid with
    | none => [Part.rows v.grid.toList {}]
    | some (mainGrid, cur, pen) =>
      [Part.rows mainGrid.toList {},
        .bytes
          (Render.penSgr pen ++ Render.csiNum2 (cur.y + 1) (cur.x + 1) 0x48 ++
            Render.pendingAnsi v.cols mainGrid cur (cur.y + 1) pen ++
            Render.csiPriv 1049 0x68 ++
            header),
        .rows v.grid.toList {}]
  { parts := .bytes before :: screens ++ [.bytes title, .text v.title.toSlice, .bytes after] }

/-- One bounded step. Empty output advances a stage or renders one row; callers
continue until there are bytes or `none`. For a positive budget every successful
step strictly decreases the work measure, including those empty transitions. -/
def next (budget : Nat) (p : Plan) : Option (Render.Bytes × Plan) :=
  match p.pending with
  | _ :: _ => some (p.pending.take budget, { p with pending := p.pending.drop budget })
  | [] =>
    match p.parts with
    | [] => none
    | .bytes bytes :: parts => some ([], { parts, pending := bytes })
    | .text text :: parts =>
      if text.isEmpty then some ([], { parts })
      else
        -- At most 4096 scalars (16384 UTF-8 bytes), even for an arbitrarily
        -- long accepted title. The slice keeps the original string shared.
        some
          ([],
            { parts := .text (text.drop 4096) :: parts
              pending := Render.utf8s (text.take 4096).copy.toList })
    | .rows [] _ :: parts => some ([], { parts })
    | .rows (row :: rows) pen :: parts =>
      let (bytes, pen') := Render.rowAnsi row pen
      some
        ([],
          { parts := .rows rows pen' :: parts
            pending := bytes ++ (if rows.isEmpty then [] else [0x0D, 0x0A]) })

/-- The following byte buffer shares a cap with the existing front buffer.
Reserving one whole frame lets replay progress even when following output is
full; increasing the front buffer is never needed to append a replay frame. -/
def followingCap (cap frame front : Nat) : Nat := cap - max frame front

end Linger.Core.Replay
