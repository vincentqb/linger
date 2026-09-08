module

public import E2E.Harness

public section

/-! # E2E.Coverage — coverage of the *code* by the theorems, enforced not reviewed

Ported from `tests/coverage.py`, the last Python in the tree. Two checks, both
ratchets; `tests/e2e.sh` runs this and fails on either.

WHY THIS EXISTS, AND WHAT IT REPLACED. The gate before it grepped all of
`Theorems/` for each pure-core definition's name and counted misses. That cannot
tell a claim from a word: `Render.history` — a byte stream the binary writes to the
user's terminal — passed it on the strength of "history" appearing in a doc comment
in `Theorems/Session.lean`. Nine of the ten it *did* flag had zero mentions, so it
was measuring "is this name absent entirely", not "is anything proved".

**Check 1** (`statements`) looks only inside theorem STATEMENTS — the text between
`theorem <name>` and the `:=`/`by` that opens the proof. A name that appears only in
a proof, a comment or a section header does not count.

**Check 2** (`emitters`) answers "are we proving things about the code that runs".
The runtime's byte-emitting surface is small and enumerable: every `Render.<f>`
referenced outside `Linger/Core/Render.lean` is a stream some code path actually
writes to a terminal. Each must be in `emitters` below with either a theorem that
constrains it or a stated limitation. A new emitter wired into the runtime fails the
gate until it is classified.

Neither check can be satisfied by writing prose.

PORTED TEXTUALLY, ON PURPOSE. This is the same scan the Python did, in Lean, so
every measured number is unchanged and the caps keep their meaning. The stronger
design is to stop scanning text at all: import the `Theorems` environment and ask
whether each `Linger.Core` constant appears in any theorem's *type*, which is
semantic, needs no comment-stripping, and cannot be fooled by formatting. That
changes the measure — and therefore the cap, which would need re-justifying — so it
belongs in its own commit, not folded into the port. -/

namespace E2E.Coverage

open E2E.Harness

/-! ## Ratchet 1

Pure-core defs named by no theorem statement. Only ever goes DOWN without
discussion; raising it is a deliberate, reviewable edit that says "new surface, no
claim yet".

`rowSlot` was briefly at 22 while its claim was pending; `rowAnsi_writes_row` and
the `rowSlot_eq_*` equations now name it. Down to 20 with `size_defaultTabs`, which
`restore_tabs_any` needs as its ruler-length witness — the ratchet tightens when a
claim lands, so it does. 19 → 16 on 2026-08-29 (pin-the-gaps item 4): the width
tables `isWide`/`isZeroWidth` were named nowhere in the repo, and the per-clause
edge pins in `Theorems/Vt.lean` claim both. The cap is the measured count with ZERO
headroom — it had one free slot before, which is a slot a new unclaimed def can
occupy silently, and every other ratchet in `tests/e2e.sh` is exact. -/
def statementCap : Nat := 16

/-- Every byte stream the runtime emits, and what backs it. A `theorem` entry must
also appear in a theorem statement (checked below); a `limitation` entry must carry
a reason and is the honest alternative to a silent hole. -/
inductive Backing where
  | theorem (why : String)
  | limitation (why : String)

def emitters : List (String × Backing) :=
  [("restore", .theorem
      "restore_grounds / restore_u8_zero / restore_modes_any / restore_pen_any / \
       restore_sticky_any / restore_cursor_any / restore_grid_any / restore_tabs_any \
       — receiver-quantified for the parser, the decoder, the screen cells, the tab \
       ruler and every restored field but the title and the DECSC slot"),
   ("leaveAnsi", .theorem
      "leave_canonical / leave_canonical_all — parser, modes, region, charsets, \
       screen and pen, for any receiver"),
   ("utf8s", .theorem
      "utf8s_no_ctl / utf8s_no_esc / utf8s_no_esc_bel / Session.utf8s_no_frame — \
       every emitted byte is >= 0x20 and not DEL, so no scrubbed text can carry an \
       escape, a BEL, or a tab/newline framing byte. Reached from outside Render by \
       Session.infoText, which frames listing records with it"),
   ("history", .theorem
      "history_framing / history_lines / history_records — every byte is a line \
       terminator or printable content, the newline count is the row count, and \
       linesLF splits the stream into exactly the rows' texts in order, so a cell \
       cannot forge a line however the session's program filled the grid"),
   ("screenText", .theorem
      "screenText_framing / screenText_lines / screenText_records — the capture \
       stream (`linger capture`): newline count = grid row count, and the parse \
       contract (line k IS rowText of row k), with history_screenText_suffix tying \
       it byte-for-byte to the transcript's tail. Grid-only")]

/-! ## Text scanning

No regex in Lean core, so these are hand-rolled — and each one is doing exactly
what the Python's corresponding pattern did, deliberately including the places that
pattern was loose (non-nested block comments), so the numbers cannot shift. -/

/-- Is `c` part of an identifier? The word boundary both checks rely on. -/
def identChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- Does `needle` occur in `hay` bounded by non-identifier characters?

`\b<name>\b` in the Python. A plain substring test would count `charWidth` as
claiming `width`, which is the whole reason the boundary is here. -/
def hasWord (hay needle : String) : Bool :=
  let h := hay.toList
  let n := needle.toList
  let len := n.length
  let rec go (pre : Option Char) (rest : List Char) : Bool :=
    if rest.take len == n then
      let after := (rest.drop len).head?
      let okBefore := match pre with | none => true | some c => !identChar c
      let okAfter := match after with | none => true | some c => !identChar c
      if okBefore && okAfter then true
      else match rest with
        | [] => false
        | c :: t => go (some c) t
    else match rest with
      | [] => false
      | c :: t => go (some c) t
  len > 0 && go none h

/-- Source with `/- … -/` blocks (docstrings included) and `--` line comments
removed.

Not cosmetic: it is what makes both checks honest. Without it check 1 counts a
definition as claimed when its name appears in a DOCSTRING, which is the exact
defect this gate replaced — and check 2 reported `Render.rowAnsi`, `rowText` and
`safeChar` as runtime-emitted because `Linger/Core/Vt.lean` *discusses* them in
comments. A gate that reads prose is a gate that can be satisfied by writing prose.

Non-nested, matching the Python's non-greedy block pattern: the shortest closing
delimiter wins. (This docstring cannot spell those delimiters — writing the closing
one inside a docstring ends it early, which is how this line first failed.) -/
partial def stripComments (s : String) : String :=
  let rec block (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '/' :: '-' :: t =>
      let rec close (r : List Char) : List Char :=
        match r with
        | [] => []
        | '-' :: '/' :: t' => t'
        | _ :: t' => close t'
      block (close t) (' ' :: acc)
    | '-' :: '-' :: t =>
      let rec eol (r : List Char) : List Char :=
        match r with
        | [] => []
        | '\n' :: t' => '\n' :: t'
        | _ :: t' => eol t'
      block (eol t) (' ' :: acc)
    | c :: t => block t (c :: acc)
  String.ofList (block s.toList [])

/-- Every `.lean` file under `root`, recursively. `Theorems/Render/*` is why this is
recursive — the Python needed `rglob` for the same reason. -/
partial def leanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut acc := #[]
  for entry in ← root.readDir do
    if ← entry.path.isDir then
      acc := acc ++ (← leanFiles entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push entry.path
  return acc

/-- Strip a leading `@[expose] `, `private ` or `public ` from a declaration line. -/
def dropModifiers (line : String) : String :=
  let l := if line.startsWith "@[expose] " then (line.drop 10).toString else line
  if l.startsWith "private " then (l.drop 8).toString
  else if l.startsWith "public " then (l.drop 7).toString
  else l

/-- The name a declaration line declares, namespace stripped to its last component
(what the Python did with sed).

The dot must be part of the token scan and only then stripped: taking `identChar`
alone stops at the namespace separator, so `def Vt.feedBytes` reads as `Vt` — which
collapsed 259 defs to 193 and made the ratchet measure LESS. Caught by diffing this
gate against the Python one before deleting it. -/
def declName (afterKeyword : String) : String :=
  let tok := ((afterKeyword.dropWhile (· == ' ')).toString.takeWhile
    (fun c => identChar c || c == '.')).toString
  (tok.splitOn ".").getLast!

/-- Names of the pure core's definitions — the census the ratchet is over.

The module system lets a decl wear `@[expose]` / `public` / `private`; the blanket
`public section` posture keeps most as a bare `def`, but e.g. `@[expose] def
Vt.applySgr` must not silently leave the census, or the ratchet starts measuring
less. -/
def coreDefs : IO (Array String) := do
  let mut names : Array String := #[]
  for f in ← leanFiles (System.FilePath.mk "Linger/Core") do
    for line in (← IO.FS.readFile f).splitOn "\n" do
      let l := dropModifiers line
      if l.startsWith "def " then
        let n := declName (l.drop 4).toString
        if !n.isEmpty && !names.contains n then names := names.push n
  return names.qsort (· < ·)

/-- The text of every theorem statement in `Theorems/`, concatenated.

A statement runs from `theorem <name>` to the `:=` or ` by ` that opens the proof;
continuation lines are indented, which is what bounds the scan. -/
def theoremStatements : IO String := do
  let mut out := ""
  for f in ← leanFiles (System.FilePath.mk "Theorems") do
    let src := stripComments (← IO.FS.readFile f)
    let lines := src.splitOn "\n"
    let mut capturing := false
    for line in lines do
      let l := dropModifiers line
      let starting := l.startsWith "theorem "
      if starting then capturing := true
      else if capturing && !(line.startsWith " " || line.startsWith "\t") then
        capturing := false
      if capturing then
        -- cut at whatever opens the proof, and stop capturing there
        let piece := line
        let cutAt (hay sep : String) : Option Nat :=
          let hs := hay.splitOn sep
          if hs.length ≥ 2 then some hs[0]!.length else none
        let cuts := [cutAt piece ":=", cutAt piece " by ",
                     if piece.endsWith " by" then some (piece.length - 3) else none]
        match (cuts.filterMap id).min? with
        | some k =>
          out := out ++ " " ++ (piece.take k).toString
          capturing := false
        | none => out := out ++ " " ++ piece
  return out

/-- `Render.<f>` referenced anywhere the runtime can reach, i.e. outside the module
that defines them. `Linger/Core/Session.lean` counts: it is pure, but it is what the
daemon calls to build what a client is sent. -/
def runtimeEmitters : IO (Array String) := do
  let mut refs : Array String := #[]
  let mut files ← leanFiles (System.FilePath.mk "Linger")
  files := files.push (System.FilePath.mk "Main.lean")
  for f in files do
    if f.fileName == some "Render.lean" && f.parent.map (·.fileName) == some (some "Core") then
      continue
    if !(← f.pathExists) then continue
    let src := stripComments (← IO.FS.readFile f)
    for chunk in (src.splitOn "Render.").tail! do
      let n := (chunk.takeWhile identChar).toString
      if !n.isEmpty && !refs.contains n then refs := refs.push n
  -- A *stream* is a def whose result type is `Bytes` or `String`; `safeChar` and
  -- friends are helpers inside the construction, not something anyone writes out.
  let renderSrc := stripComments (← IO.FS.readFile (System.FilePath.mk "Linger/Core/Render.lean"))
  let mut streams : Array String := #[]
  for line in renderSrc.splitOn "\n" do
    let l := dropModifiers line
    if l.startsWith "def " && (has l ": Bytes" || has l ": String") then
      let n := declName (l.drop 4).toString
      if !n.isEmpty then streams := streams.push n
  return (refs.filter (streams.contains ·)).qsort (· < ·)

def run : IO UInt32 := do
  let mut fails : Array String := #[]

  -- Check 1 — statement-level claim ratchet
  let defs ← coreDefs
  let blob ← theoremStatements
  let unclaimed := defs.filter (fun d => !hasWord blob d)
  IO.println s!"core defs {defs.size}; named by no theorem STATEMENT: \
    {unclaimed.size} (cap {statementCap})"
  IO.println ("  " ++ String.intercalate " " unclaimed.toList)
  if unclaimed.size > statementCap then
    fails := fails.push s!"unclaimed core surface grew to {unclaimed.size} \
      (cap {statementCap}); add a claim or bump the cap deliberately"

  -- Check 2 — every runtime-emitted byte stream is classified
  let found ← runtimeEmitters
  IO.println s!"runtime-emitted byte streams: {String.intercalate " " found.toList}"
  for name in found do
    match (emitters.find? (·.1 == name)).map (·.2) with
    | none =>
      fails := fails.push s!"the runtime emits `Render.{name}` and it is in neither \
        the theorem list nor the limitation list of E2E/Coverage.lean — classify it \
        (that unclassified state is what let the hand-back ship)"
    | some (.theorem why) =>
      if !hasWord blob name then
        fails := fails.push s!"`Render.{name}` is listed as theorem-backed but \
          appears in no theorem statement"
      else IO.println s!"  {name}: proved — {(why.take 60).toString}…"
    | some (.limitation why) =>
      IO.println s!"  {name}: bounded — {(why.take 60).toString}…"
  for (name, _) in emitters do
    if !found.contains name then
      fails := fails.push s!"E2E/Coverage.lean classifies `Render.{name}` but the \
        runtime no longer emits it — delete the entry so the list stays a \
        description of the code"

  for msg in fails do
    IO.eprintln s!"COVERAGE FAIL: {msg}"
  IO.println s!"FAILURES: {fails.size}"
  return if fails.isEmpty then 0 else 1

end E2E.Coverage
