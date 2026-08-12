import Zmx.Core.Name
import Zmx.Core.Remote
/-! # Zmx.Core.Tui — the session manager, as data

Bare `lzmx` opens this: an fzf-shaped picker over sessions (local and
remote), with a live preview pane. Philosophy follows zmx-session-
manager: the TUI *manages* sessions; attaching execs the plain client,
so the TUI is never in the byte path between you and your pty.

Interaction (one mode, like fzf — from the maintainer's own tooling):
* type      → filter; the query doubles as a new-session name
* ↑/↓, C-p/C-n, C-k/C-j → move selection
* enter     → attach selection, or create+attach the query if no match
* C-x C-x   → kill selection (second press confirms)
* C-r       → refresh
* esc / C-c / C-q → quit

Pure: `step : State → Event → State × List Effect` and
`render : State → String` (full-frame ANSI, Dracula, status on top —
the fixed modern default; no configuration).
-/

namespace Zmx.Core.Tui

/-- Where a session lives. -/
inductive Host where
  | local
  | remote (host : String)
  deriving Repr, DecidableEq, Inhabited

inductive RowState where
  | live
  | resumable
  deriving Repr, DecidableEq, Inhabited

structure Row where
  name : String
  host : Host := .local
  state : RowState := .live
  pid : String := ""
  cmd : String := ""
  labels : List (String × String) := []
  deriving Repr, DecidableEq, Inhabited

/-- Build a list row from a session's *socket name* plus whatever its
`info` reply happened to contain. The name comes from the filesystem,
never from the reply: a daemon too busy to answer within the timeout
(or one answering nonsense) still gets a correctly-named row, and no
reply can rename or blank another session's row. See §Row. -/
def rowOfInfo (sockName : String) (kvs : List (String × String)) (host : Host := .local)
    : Row :=
  let get := fun k => ((kvs.find? (·.1 == k)).map (·.2)).getD ""
  { name := Name.sanitize sockName
    host
    state := .live          -- it answered the socket, so it exists
    pid := Zmx.Core.Remote.scrub (get "pid")
    cmd := Zmx.Core.Remote.scrub (get "cmd")
    labels := kvs.filterMap (fun (k, v) =>
      if k.startsWith "label." then
        some (Zmx.Core.Remote.scrub (k.drop 6).toString, Zmx.Core.Remote.scrub v)
      else none) }

structure State where
  rows : List Row := []
  query : String := ""
  /-- index into `matches` (not `rows`). -/
  sel : Nat := 0
  preview : List String := []
  /-- name+host the preview belongs to (stale previews aren't shown). -/
  previewFor : Option (String × Host) := none
  cols : Nat := 80
  rows_ : Nat := 24
  killArmed : Bool := false
  message : String := ""
  deriving Repr, Inhabited

inductive Key where
  | char (c : Char)
  | enter
  | backspace
  | up
  | down
  | ctrlN | ctrlP | ctrlJ | ctrlK | ctrlX | ctrlR
  | esc | ctrlC | ctrlQ
  | other
  deriving Repr, DecidableEq

inductive Event where
  | key (k : Key)
  | rowsUpdated (rows : List Row)
  | previewUpdated (name : String) (host : Host) (lines : List String)
  | resized (cols rows : Nat)
  deriving Repr

inductive Effect where
  | quit
  | attach (name : String) (host : Host)
  | create (name : String)
  | kill (name : String) (host : Host)
  | refresh
  | fetchPreview (name : String) (host : Host)
  deriving Repr, DecidableEq

def maxQuery : Nat := 64

/-- Subsequence match, case-insensitive — the useful core of fuzzy. -/
def fuzzy (query s : String) : Bool :=
  let rec go : List Char → List Char → Bool
    | [], _ => true
    | _ :: _, [] => false
    | q :: qs, c :: cs =>
      if q.toLower == c.toLower then go qs cs else go (q :: qs) cs
  go query.toList s.toList

def State.matches (st : State) : List Row :=
  st.rows.filter (fun r => fuzzy st.query r.name)

def State.selected (st : State) : Option Row :=
  st.matches[st.sel]?

/-- Clamp selection into the match list (call after anything that
changes `rows` or `query`). §Bound(tui): `sel` never escapes. -/
def State.clampSel (st : State) : State :=
  let n := st.matches.length
  { st with sel := if n == 0 then 0 else min st.sel (n - 1) }

/-- Ask for the selected row's preview if we don't already show it. -/
def previewEffects (st : State) : List Effect :=
  match st.selected with
  | none => []
  | some r =>
    if st.previewFor == some (r.name, r.host) then []
    else [.fetchPreview r.name r.host]

def step (st : State) (ev : Event) : State × List Effect :=
  match ev with
  | .rowsUpdated rows =>
    let st := ({ st with rows, message := "" }).clampSel
    (st, previewEffects st)
  | .previewUpdated name host lines =>
    -- accept only if still relevant
    if st.selected.any (fun r => r.name == name && r.host == host) then
      ({ st with preview := lines, previewFor := some (name, host) }, [])
    else (st, [])
  | .resized c r => ({ st with cols := c, rows_ := r }, [])
  | .key k =>
    let st := { st with message := "" }
    match k with
    | .esc | .ctrlC | .ctrlQ => (st, [.quit])
    | .up | .ctrlP | .ctrlK =>
      let st := ({ st with sel := st.sel - 1, killArmed := false }).clampSel
      (st, previewEffects st)
    | .down | .ctrlN | .ctrlJ =>
      let st := ({ st with sel := st.sel + 1, killArmed := false }).clampSel
      (st, previewEffects st)
    | .char c =>
      if st.query.length ≥ maxQuery then (st, [])
      else
        let st := ({ st with query := st.query.push c, sel := 0,
                             killArmed := false }).clampSel
        (st, previewEffects st)
    | .backspace =>
      let st := ({ st with query := String.ofList st.query.toList.dropLast, sel := 0,
                           killArmed := false }).clampSel
      (st, previewEffects st)
    | .enter =>
      (match st.selected with
       | some r => (st, [.attach r.name r.host])
       | none =>
         if st.query.isEmpty then (st, [])
         else (st, [.create (Name.sanitize st.query)]))
    | .ctrlX =>
      (match st.selected with
       | none => (st, [])
       | some r =>
         if st.killArmed then
           ({ st with killArmed := false, message := s!"killed {r.name}" },
            [.kill r.name r.host, .refresh])
         else
           ({ st with killArmed := true,
                      message := s!"C-x again to kill {r.name}" }, []))
    | .ctrlR => ({ st with killArmed := false }, [.refresh])
    | .other => (st, [])

/-! ## Rendering — Dracula, status top, list left, preview right -/

def dBg : String := "\x1b[48;2;40;42;54m"        -- #282a36
def dGray : String := "\x1b[48;2;68;71;90m"      -- #44475a
def dFg : String := "\x1b[38;2;248;248;242m"     -- #f8f8f2
def dMuted : String := "\x1b[38;2;98;114;164m"   -- #6272a4
def dPinkBg : String := "\x1b[48;2;255;121;198m" -- #ff79c6
def dDarkFg : String := "\x1b[38;2;40;42;54m"
def dGreen : String := "\x1b[38;2;80;250;123m"   -- #50fa7b
def dYellow : String := "\x1b[38;2;241;250;140m" -- #f1fa8c
def dRed : String := "\x1b[38;2;255;85;85m"      -- #ff5555
def dCyan : String := "\x1b[38;2;139;233;253m"   -- #8be9fd
def rst : String := "\x1b[0m"

/-- Truncate-or-pad to exactly `n` display columns (¹ assumes width-1
chars: names/commands are sanitized ASCII-ish; the preview pane is the
only place wide glyphs appear and it's right-padded only). -/
def fit (n : Nat) (s : String) : String :=
  let cs := s.toList.take n
  String.ofList (cs ++ List.replicate (n - cs.length) ' ')

def stateColor : RowState → String
  | .live => dGreen
  | .resumable => dYellow

def hostLabel : Host → String
  | .local => ""
  | .remote h => s!"@{h}"

/-- One row line in the list pane. -/
def rowLine (width : Nat) (isSel : Bool) (r : Row) : String :=
  let mark := match r.state with
    | .live => "●"
    | .resumable => "○"
  let label := fit (width - 4) s!"{r.name}{hostLabel r.host}"
  if isSel then
    s!"{dPinkBg}{dDarkFg} {mark} {label} {rst}"
  else
    s!"{dBg}{stateColor r.state} {mark} {dFg}{label} {rst}"

/-- The whole frame as one ANSI string (full repaint: home, draw, no
clear — every cell is written, so no flicker and no stale cells). -/
def render (st : State) : String :=
  let w := max st.cols 40
  let h := max st.rows_ 6
  let listW := min (w * 2 / 5) 40
  let prevW := w - listW - 1
  let bodyH := h - 3  -- status + query + hints
  let ms := st.matches
  -- status bar
  let live := (st.rows.filter (·.state == .live)).length
  let res := (st.rows.filter (·.state == .resumable)).length
  let counts := s!"{live} live" ++ (if res > 0 then s!" · {res} resumable" else "")
  let msg := if st.message.isEmpty then counts else st.message
  let status := s!"{dGray}{dFg} lzmx {rst}{dBg}{dMuted} {fit (w - 7) msg}{rst}"
  -- query line — placeholder guidance while empty, so the box doesn't
  -- read like a shell prompt
  let qbody := if st.query.isEmpty
    then "type a name, then Enter, to start a session"
    else st.query
  let qcolor := if st.query.isEmpty then dMuted else dFg
  let qline := s!"{dBg}{dCyan} ❯ {qcolor}{fit (w - 4) qbody}{rst}"
  -- body
  let blank := s!"{dBg}{fit w ""}{rst}"
  let body :=
    if st.rows.isEmpty then
      -- first run / nothing to manage: teach the model instead of
      -- drawing a lone divider column (which reads as "broken")
      let c := bodyH / 2
      (List.range bodyH).map (fun i =>
        if i == c then
          s!"{dBg}{dFg}{fit w "   No sessions yet."}{rst}"
        else if i == c + 1 then
          s!"{dBg}{dMuted}{fit w "   Type a name above and press Enter to create one,"}{rst}"
        else if i == c + 2 then
          s!"{dBg}{dMuted}{fit w "   or run  lzmx attach <name>  from your shell.  (Esc quits)"}{rst}"
        else blank)
    else
      -- list + preview, split by the divider
      let scroll := if st.sel ≥ bodyH then st.sel - bodyH + 1 else 0
      (List.range bodyH).map (fun i =>
        let idx := i + scroll
        let listCell := match ms[idx]? with
          | some r => rowLine listW (idx == st.sel) r
          | none =>
            -- query hides everything: point at the create action
            if i == 0 && ms.isEmpty && !st.query.isEmpty then
              s!"{dBg}{dMuted}{fit listW s!" (no match — Enter creates ‘{st.query}’)"}{rst}"
            else s!"{dBg}{fit listW ""}{rst}"
        let prevCell := match st.preview[i]? with
          | some line => s!"{dBg}{dFg}{fit prevW line}{rst}"
          | none => s!"{dBg}{fit prevW ""}{rst}"
        s!"{listCell}{dBg}{dMuted}│{rst}{prevCell}")
  let hints := s!"{dBg}{dMuted} {fit (w - 1) "Enter attach/create · type to filter or name · C-x C-x kill · esc quit"}{rst}"
  "\x1b[H" ++ String.intercalate "\r\n" ([status, qline] ++ body ++ [hints])

end Zmx.Core.Tui
