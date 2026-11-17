module

public import Terminal.CoreCode.Vt
import Terminal.CoreCode.Render
-- Replay is a second consumer of the renderer's sealed snapshot. It shares
-- rows; it never changes a terminal or exposes its representation.
import all Terminal.CoreCode.Vt

instance : Repr String.Slice where
  reprPrec s _ := repr (s.str, s.startInclusive.offset.byteIdx, s.endExclusive.offset.byteIdx)

deriving instance DecidableEq for String.Slice

public section

namespace Terminal.Replay

open Terminal.Vt

private inductive Part where
  | bytes (value : Render.Bytes)
  | rows (value : List Row) (pen : Pen)
  | text (value : String.Slice)
  deriving Repr, DecidableEq

/-- A captured repaint. The remaining grids share immutable rows with the
terminal at attach time. `pending` holds one stage, row or bounded title chunk;
neither the complete repaint nor an output-effect backlog is stored. -/
structure PlanRec where
  private parts : List Part
  private pending : Render.Bytes := []
  deriving Repr, DecidableEq

/-- A captured repaint, as the headline theorems name it: a definition over the sealed record
`PlanRec`, because `Challenge.lean` declares the type as a hole the program fills. -/
abbrev Plan : Type := PlanRec

/-- Capture at the pure event point, before later messages can resize or feed
the terminal. Literal stages are renderer control/history bytes; screen paints
remain shared rows and the title remains a shared slice until demanded. The repaint is one
synchronized update: its first step sends `Render.syncBegin` alone, and its last bytes are
`Render.syncEnd`, so a terminal that knows DEC mode 2026 shows it whole. -/
def start (v : Vt) : Plan :=
  let header := Render.csiNum 0 0x6D ++ (Render.csiB ++ [0x48])
  let before :=
    Render.prologueAnsi v ++ Render.csiNum 0 0x6D ++ Render.csiNum 2 0x4A ++
      Render.scrollbackAnsi v ++
      header
  let title :=
    Render.savedAnsi v ++ Render.regionAnsi v ++ Render.tabsAnsi v ++ Render.escB ++
      [0x5D, 0x32, 0x3B]
  let after :=
    [0x07] ++ Render.modesAnsi v ++ Render.charsetAnsi v ++ Render.penSgr v.getPen ++
      Render.cursorAnsi v ++
      Render.cursorPendingAnsi v ++
      Render.syncEnd
  let screens :=
    match v.altGrid with
    | none => [Part.rows v.grid.toList {}]
    | some (mainGrid, ms) =>
      [Part.rows mainGrid.toList {},
        .bytes
          (Render.parkAnsi v.cols mainGrid ms ++ Render.csiPriv 1049 0x68 ++
            Render.originOffAnsi ms ++
            header),
        .rows v.grid.toList {}]
  { parts := .bytes before :: screens ++ [.bytes title, .text v.title.toSlice, .bytes after]
    pending := Render.syncBegin }

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

end Terminal.Replay
