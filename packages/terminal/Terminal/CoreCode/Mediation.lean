module

public import Terminal.CoreCode.Vt
import Terminal.CoreCode.Render
-- `Vt`'s fields are `private` (the seal). Mediation
-- is a toolkit module and reads cursor/mode state to answer owned queries,
-- so it is a friend by construction, not an escape hatch.
import all Terminal.CoreCode.Vt

public section

/-! # Terminal.Mediation — terminal mediation

`Vt` remains the screen model. This module adds the other half of owning a
PTY: recognizing the small documented query profile, replying to the child,
and withholding only those owned requests from presentation clients.
Everything else is emitted byte-for-byte. Beside the scanner, it hears what
the output tells of its program: a bell or a notification, and a shell's
marks. Title updates are `Terminal.Title`.

Potential CSI/OSC/DCS requests are bounded. Once a sequence is known to be
unowned, passthrough states emit each subsequent byte immediately, so kitty
APC and sixel DCS payloads take constant scanner memory and linear time.
-/

namespace Terminal.Mediation

open Terminal.Vt Terminal.Render

/-- The bell byte, which also terminates OSC. -/
abbrev BEL : UInt8 := 0x07

/-- The final byte of the string terminator `ESC \`. -/
abbrev STFinal : UInt8 := 0x5C

/-! ## Exact profile replies -/

/-- Primary device attributes reply: a VT100 with advanced video. -/
def da1Reply : Bytes := [ESC, 0x5B, 0x3F, 0x31, 0x3B, 0x32, 0x63]

/-- Secondary device attributes reply: `CSI > 0 ; 0 ; 0 c`. -/
def da2Reply : Bytes := [ESC, 0x5B, 0x3E, 0x30, 0x3B, 0x30, 0x3B, 0x30, 0x63]

/-- Device status reply: the terminal is OK (`CSI 0 n`, or `CSI ? 0 n` when private). -/
private def statusReply (private_ : Bool) : Bytes :=
  [ESC, 0x5B] ++ (if private_ then [0x3F] else []) ++ [0x30, 0x6E]

/-- The 1-based row a cursor position report gives, relative to the region under DECOM. Origin
mode and the region's top are read through the terminal's public surface. -/
private def cprRow (v : Vt) : Nat :=
  if v.getModes.origin then if v.cursor.y < (stick v).top then 1 else v.cursor.y - (stick v).top + 1
  else v.cursor.y + 1

/-- Cursor position report `CSI row ; column R`, with `?` when private. -/
private def cprReply (v : Vt) (private_ : Bool) : Bytes :=
  [ESC, 0x5B] ++ (if private_ then [0x3F] else []) ++ digits (cprRow v) ++ [0x3B] ++
    digits (v.cursor.x + 1) ++
    [0x52]

/-- The version `linger --version`, `TERM_PROGRAM_VERSION` and XTVERSION report. -/
def versionNumber : String := "0.1.0"

/-- XTVERSION reply: `DCS > | linger 0.1.0 ST`; `Terminal.Tests.Mediation` ties these
bytes to
`versionNumber`. -/
def versionReply : Bytes :=
  [ESC, 0x50, 0x3E, 0x7C, 0x6C, 0x69, 0x6E, 0x67, 0x65, 0x72, 0x20, 0x30, 0x2E, 0x31, 0x2E, 0x30,
    ESC, STFinal]

/-- Text-area size reply for `CSI 18 t`: `CSI 8 ; rows ; cols t`. -/
private def textAreaReply (v : Vt) : Bytes :=
  [ESC, 0x5B, 0x38, 0x3B] ++ digits v.rows ++ [0x3B] ++ digits v.cols ++ [0x74]

/-- Fixed virtual palette reply for OSC 10/11/12. `selector` is the final
ASCII digit and `hex` is `f` for white or `0` for black. -/
private def paletteReply (selector hex : UInt8) : Bytes :=
  [ESC, 0x5D, 0x31, selector, 0x3B, 0x72, 0x67, 0x62, 0x3A] ++ List.replicate 4 hex ++ [0x2F] ++
    List.replicate 4 hex ++
    [0x2F] ++
    List.replicate 4 hex ++
    [ESC, STFinal]

/-- The legal XTGETTCAP payload alphabet: hex digits and the `;` that
separates capability names. Everything a well-formed request carries. -/
private def capByte (b : UInt8) : Bool :=
  (0x30 ≤ b && b ≤ 0x39) || (0x41 ≤ b && b ≤ 0x46) || (0x61 ≤ b && b ≤ 0x66) || b == 0x3B

/-- XTGETTCAP is answered negatively for every capability, echoing the
requested name so the child knows *which* is unsupported. The echo is
**filtered to the legal alphabet**, because the reply is written into the
child's own input (`Session.step .ptyOut → .writePty`), and a request is
child-controlled output — a `cat` of a hostile file, an ssh stream, a log
tail. A raw payload could carry a CR and a shell command; on a cooked-mode
tty the CR commits a line, so echoing it verbatim would let untrusted output
run a command (terminal-reply injection). A conforming request is hex, so the
filter is the identity on it; a malformed one loses exactly the bytes that
could terminate a line. `feed_replies_noNl` states the guarantee this
buys: no reply linger ever writes to the child contains a line terminator. -/
def xtgetcapReply (payload : Bytes) : Bytes :=
  [ESC, 0x50, 0x30, 0x2B, 0x72] ++ payload.filter capByte ++ [ESC, STFinal]

/-- DECRQSS reply: every setting request is answered as invalid. -/
def decrqssReply : Bytes := [ESC, 0x50, 0x30, 0x24, 0x72, ESC, STFinal]

/-- A complete request's classification: passed through, or owned with its reply. -/
inductive Decision where
  /-- Outside the profile: clients receive the sequence unchanged. -/
  | unowned
  /-- In the profile: the sequence is withheld from clients and `reply` goes to the child. -/
  | owned (reply : Bytes)
  deriving Repr, DecidableEq

/-- Exact CSI rows from the normative profile. No prefix or parameter
normalization is intentional: every unlisted spelling is passthrough. The title reports
`CSI 20 t` and `CSI 21 t` are owned with no reply: a client's terminal would answer with the
title it shows, which the program would read as typed. -/
def classifyCsi (v : Vt) (seq : Bytes) : Decision :=
  if seq == [ESC, 0x5B, 0x63] || seq == [ESC, 0x5B, 0x30, 0x63] then .owned da1Reply
  else
    if seq == [ESC, 0x5B, 0x3E, 0x63] || seq == [ESC, 0x5B, 0x3E, 0x30, 0x63] then .owned da2Reply
    else
      if seq == [ESC, 0x5B, 0x35, 0x6E] then .owned (statusReply false)
      else
        if seq == [ESC, 0x5B, 0x3F, 0x35, 0x6E] then .owned (statusReply true)
        else
          if seq == [ESC, 0x5B, 0x36, 0x6E] then .owned (cprReply v false)
          else
            if seq == [ESC, 0x5B, 0x3F, 0x36, 0x6E] then .owned (cprReply v true)
            else
              if seq == [ESC, 0x5B, 0x3E, 0x71] || seq == [ESC, 0x5B, 0x3E, 0x30, 0x71] then
                .owned versionReply
              else
                if seq == [ESC, 0x5B, 0x31, 0x38, 0x74] then .owned (textAreaReply v)
                else
                  if
                      seq == [ESC, 0x5B, 0x3F, 0x75] || seq == [ESC, 0x5B, 0x32, 0x30, 0x74] ||
                        seq == [ESC, 0x5B, 0x32, 0x31, 0x74] then
                    .owned []
                  else .unowned

/-- Whether bytes end a request: BEL, or ST. -/
private def terminated (rest : Bytes) : Bool := rest == [BEL] || rest == [ESC, STFinal]

/-- A selection, any bytes but `;`, then `; ?` and the terminator: what follows `52 ;` in a
clipboard query. -/
private def selectionQuery : Bytes → Bool
  | [] => false
  | b :: rest =>
    if b == 0x3B then rest.head? == some 0x3F && terminated rest.tail else selectionQuery rest

/-- Decimal digits, then `; ?` and the terminator. -/
private def digitsQuery : Bytes → Bool
  | [] => false
  | b :: rest =>
    if b == 0x3B then rest.head? == some 0x3F && terminated rest.tail
    else 0x30 ≤ b && b ≤ 0x39 && digitsQuery rest

/-- A decimal colour index, then `; ?` and the terminator: what follows `4 ;` or `5 ;` in a
colour query. -/
private def indexQuery : Bytes → Bool
  | [] => false
  | b :: rest => 0x30 ≤ b && b ≤ 0x39 && digitsQuery rest

/-- The OSC queries no terminal answers to the program, by what follows their `ESC ]`: a
client's terminal would answer them from what it keeps for its user, and linger's terminal keeps
none of it. A clipboard query, `52 ; <selection> ; ?`, a palette or special colour query,
`4 ; <index> ; ?` or `5 ; <index> ; ?`, and a query of a dynamic colour past the three linger
answers, `13 ; ?` to `19 ; ?`, each ended by BEL or ST: one query per request, as xterm documents
it. -/
private def unansweredOsc : Bytes → Bool
  | 0x35 :: 0x32 :: 0x3B :: rest => selectionQuery rest
  | 0x34 :: 0x3B :: rest => indexQuery rest
  | 0x35 :: 0x3B :: rest => indexQuery rest
  | 0x31 :: d :: 0x3B :: 0x3F :: rest => 0x33 ≤ d && d ≤ 0x39 && terminated rest
  | _ => false

/-- Whether a complete request is an OSC query no terminal answers (`unansweredOsc`). -/
private def unanswered : Bytes → Bool
  | 0x1B :: 0x5D :: rest => unansweredOsc rest
  | _ => false

/-- Exact fixed-palette OSC rows, and the queries no terminal answers (`unansweredOsc`), owned
with no reply: a program's query is answered by linger's terminal or by nobody, never by a
client's, whose answer the program would read as typed input. Both BEL and ST terminate
requests; replies always use ST. A clipboard write and every other OSC pass through, as does a
request longer than `oscCap`, which the scanner releases before it ends. -/
private def classifyOsc (seq : Bytes) : Decision :=
  if
      seq == [ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, BEL] ||
        seq == [ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, ESC, STFinal] then
    .owned (paletteReply 0x30 0x66)
  else
    if
        seq == [ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, BEL] ||
          seq == [ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, ESC, STFinal] then
      .owned (paletteReply 0x31 0x30)
    else
      if
          seq == [ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, BEL] ||
            seq == [ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, ESC, STFinal] then
        .owned (paletteReply 0x32 0x66)
      else if unanswered seq then .owned [] else .unowned

/-! ## Bounded scanner -/

/-- Bytes retained but not yet sent to presentation clients. -/
private def Scan.pending : Scan → Bytes
  | .esc => [ESC]
  | .csi rev => rev.reverse
  | .osc rev _ => rev.reverse
  | .dcsIntro => [ESC, 0x50]
  | .dcsKind kind => [ESC, 0x50, kind]
  | .dcs kind payloadRev escSeen =>
    [ESC, 0x50, kind, 0x71] ++ payloadRev.reverse ++ (if escSeen then [ESC] else [])
  | _ => []

/-- One scanner step: the next state, bytes released to clients and replies to the child. -/
structure ScanStep where
  /-- The scanner's next state. -/
  scan : Scan
  /-- Bytes released to presentation clients. -/
  visible : Bytes := []
  /-- Bytes to write to the child. -/
  replies : Bytes := []
  deriving Repr, DecidableEq

/-- Complete one buffered candidate: owned requests disappear from visible
output and produce their one prescribed reply stream; unowned candidates are
released unchanged. -/
private def complete (decision : Decision) (seq : Bytes) : ScanStep :=
  match decision with
  | .unowned => { scan := .ground, visible := seq }
  | .owned reply => { scan := .ground, replies := reply }

/-- Advance only the ownership scanner. `v` is the VT state after this byte,
so a CPR samples the cursor at the query's exact stream position. -/
private def Scan.step (s : Scan) (v : Vt) (b : UInt8) : ScanStep :=
  match s with
  | .ground => if b == ESC then { scan := .esc } else { scan := .ground, visible := [b] }
  | .esc =>
    if b == 0x5B then { scan := .csi [0x5B, ESC] }
    else
      if b == 0x5D then { scan := .osc [0x5D, ESC] false }
      else
        if b == 0x50 then { scan := .dcsIntro }
        else
          if b == 0x58 || b == 0x5E || b == 0x5F then
            { scan := .strPass false, visible := [ESC, b] }
          else
            if b == ESC then { scan := .esc, visible := [ESC] }
            else { scan := .ground, visible := [ESC, b] }
  | .csi rev =>
    if b == ESC then { scan := .esc, visible := rev.reverse }
    else
      if 0x40 ≤ b && b ≤ 0x7E then
        let seq := (b :: rev).reverse
        complete (classifyCsi v seq) seq
      else
        if rev.length < csiCap then { scan := .csi (b :: rev) }
        else { scan := .csiPass, visible := (b :: rev).reverse }
  | .csiPass =>
    if b == ESC then { scan := .esc }
    else
      if 0x40 ≤ b && b ≤ 0x7E then { scan := .ground, visible := [b] }
      else { scan := .csiPass, visible := [b] }
  | .osc rev escSeen =>
    if b == BEL || (escSeen && b == STFinal) then
        let seq := (b :: rev).reverse
        complete (classifyOsc seq) seq
    else
      if rev.length < oscCap then { scan := .osc (b :: rev) (b == ESC) }
      else { scan := .oscPass (b == ESC), visible := (b :: rev).reverse }
  | .oscPass escSeen =>
    if b == BEL || (escSeen && b == STFinal) then { scan := .ground, visible := [b] }
    else { scan := .oscPass (b == ESC), visible := [b] }
  | .dcsIntro =>
    if b == 0x2B || b == 0x24 then { scan := .dcsKind b }
    else { scan := .strPass (b == ESC), visible := [ESC, 0x50, b] }
  | .dcsKind kind =>
    if b == 0x71 then { scan := .dcs kind [] false }
    else { scan := .strPass (b == ESC), visible := [ESC, 0x50, kind, b] }
  | .dcs kind payloadRev escSeen =>
    if escSeen && b == STFinal then
        let payload := payloadRev.reverse
        let seq := s.pending ++ [b]
        if kind == 0x2B then complete (.owned (xtgetcapReply payload)) seq
      else if kind == 0x24 then complete (.owned decrqssReply) seq else complete .unowned seq
    else
        let nextEsc := b == ESC
        let nextRev :=
        if b == ESC then if escSeen then ESC :: payloadRev else payloadRev
        else if escSeen then b :: ESC :: payloadRev else b :: payloadRev
        -- `(Scan.dcs kind nextRev nextEsc).pending.length`, without building that buffer
        if nextRev.length + (if nextEsc then 5 else 4) ≤ dcsCap then
        { scan := .dcs kind nextRev nextEsc }
      else { scan := .strPass nextEsc, visible := s.pending ++ [b] }
  | .strPass escSeen =>
    if escSeen && b == STFinal then { scan := .ground, visible := [b] }
    else { scan := .strPass (b == ESC), visible := [b] }

/-- Flush an incomplete prefix exactly once and reset the scanner. The bytes
have already reached `Vt`, so callers must only broadcast them. -/
def finish (s : Scan) : Bytes × Scan := (s.pending, .ground)

/-! ## A program that asks for someone

A program asks for its user as a terminal hears it: it rings the bell or posts a desktop
notification. The bell is BEL as a control: in ground, after ESC or within a control sequence,
where a terminal executes it, never the BEL that ends an OSC string, nor one within a DCS, SOS, PM
or APC string. A notification is OSC 9, `ESC ] 9 ; text`, as iTerm2 and Ghostty post it, unless
its payload is digits followed by `;`, a ConEmu sub-command such as `9;4;…` progress, or OSC 777,
`ESC ] 777 ; notify ; title ; body`, ended by BEL or ST. The mediator hears either as it scans the
byte that completes it (`Scan.hears`), beside the scanner, whose decisions it leaves as they were:
a notification still reaches every client unchanged, so the outer terminal can show its own.

A notification longer than `oscCap`, which the scanner releases unclassified, is heard as the
scanner releases it, with the text the scanner held: every buffer input fills has a cap, and this
one bounds the text kept, never whether a notification is heard. -/

/-- What one byte of the program's output tells of it asking for someone. -/
structure Heard where
  /-- The byte rang the bell, or posted a notification. -/
  asks : Bool := false
  /-- The text of the notification the byte posted: the OSC 9 text, or the OSC 777 title and
  body. -/
  notice : Option Bytes := none
  deriving Repr, DecidableEq

/-- Whether a byte is an ASCII digit. -/
private def digit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- Whether an OSC 9 text is a ConEmu sub-command instead: digits, then `;`, as `4;1;50`
reports progress. -/
def subcommand (text : Bytes) : Bool :=
  !(text.takeWhile digit).isEmpty && (text.dropWhile digit).head? == some 0x3B

/-- The text of the desktop notification an OSC payload posts, if it posts one: what follows
`9;`, unless that is a ConEmu sub-command, or what follows `777;notify;`, its title and its body,
joined by `: ` when it has both. -/
def noticeOf : Bytes → Option Bytes
  | 0x39 :: 0x3B :: text => if subcommand text then none else some text
  | 0x37 :: 0x37 :: 0x37 :: 0x3B :: 0x6E :: 0x6F :: 0x74 :: 0x69 :: 0x66 :: 0x79 :: 0x3B :: rest =>
    let title := rest.takeWhile (· != 0x3B)
    let body := (rest.dropWhile (· != 0x3B)).drop 1
    some
      (if title.isEmpty then body
      else if body.isEmpty then title else title ++ [0x3A, 0x20] ++ body)
  | _ => none

/-- The payload of an OSC the scanner holds, from its reversed buffer: the bytes after `ESC ]`,
without an ESC that may begin its terminator. -/
def heldPayload (rev : Bytes) : Bytes := (rev.dropWhile (· == ESC)).reverse.drop 2

/-- What an OSC payload tells: a notification asks, with its text, and any other payload tells
nothing. -/
def heardOsc (payload : Bytes) : Heard :=
  match noticeOf payload with
  | some text => { asks := true, notice := some text }
  | none => {}

/-- What scanning `b` from `s` hears of the program asking for someone: a bell, a BEL outside
every string, or the notification an OSC posts, as BEL or ST completes it, or, past `oscCap`, as
the scanner releases it unclassified. -/
def Scan.hears (s : Scan) (b : UInt8) : Heard :=
  match s with
  | .ground | .esc | .csi _ | .csiPass => { asks := b == BEL }
  | .osc rev escSeen =>
    if b == BEL || (escSeen && b == STFinal) then heardOsc (heldPayload rev)
    else if rev.length < oscCap then {} else heardOsc (heldPayload (b :: rev))
  | _ => {}

/-! ## A shell's marks

A shell marks its prompt and each command it runs with OSC 133, FinalTerm's semantic prompts, as
iTerm2, kitty, WezTerm, Ghostty, Windows Terminal and VS Code read them: `A` as a prompt starts,
`B` as the command's input starts, `C` as the command runs, its output following, and `D` as it
finished, each possibly followed by `;` parameters, and ended by BEL or ST. A `C` may give the
command line as kitty defines it, `cmdline_url=` and the line as UTF-8 %-escaped text, or
`cmdline=` and the line quoted as `printf %q` quotes it, and a `D` gives the command's exit
status as its first parameter, a decimal number. The mediator hears a mark as it scans the byte
that completes it (`Scan.mark`), beside the scanner, whose decisions it leaves as they were: a
mark still reaches every client unchanged.

A mark longer than `oscCap`, which the scanner releases unclassified, is heard as the scanner
releases it, from the bytes it held: the cap bounds the command line kept, never whether a mark
is heard, and a command line it cuts is not whole. A value that stops decoding gives the bytes
read before it, not whole either, so a command line tells less than the shell said, never
something else. -/

/-- How a parameter's value ends: at the `;` that begins the next parameter, with the payload,
or where it stops decoding. -/
private inductive Stop where
  /-- At the `;` that begins the next parameter: the value is whole. -/
  | semicolon
  /-- With the payload: the value is whole when the payload is. -/
  | payloadEnd
  /-- Where it stops decoding: what was read before is not the whole value. -/
  | broken

/-- A hexadecimal digit's value. -/
private def hexDigit (b : UInt8) : Option Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b - 0x30).toNat
  else
    if 0x41 ≤ b && b ≤ 0x46 then some (b - 0x37).toNat
    else if 0x61 ≤ b && b ≤ 0x66 then some (b - 0x57).toNat else none

/-- What follows `cmdline_url=` in a `C` mark, up to the `;` that ends it, with each `%` and two
hexadecimal digits decoded to the byte they stand for. A `%` without them stops it. -/
private def urlValue : Bytes → Bytes × Stop
  | [] => ([], .payloadEnd)
  | 0x3B :: _ => ([], .semicolon)
  | 0x25 :: high :: low :: rest =>
    match hexDigit high, hexDigit low with
    | some h, some l => ((UInt8.ofNat (16 * h + l)) :: (urlValue rest).1, (urlValue rest).2)
    | _, _ => ([], .broken)
  | 0x25 :: _ => ([], .broken)
  | b :: rest => (b :: (urlValue rest).1, (urlValue rest).2)

/-- Where a `printf %q` word is read: outside quotes, within single quotes, or within ANSI-C
quotes, `$'…'`. -/
private inductive Quoting where
  /-- Outside quotes. -/
  | bare
  /-- Within single quotes, which quote every byte up to the next `'`. -/
  | single
  /-- Within `$'…'`, whose backslash escapes stand for bytes. -/
  | ansi

/-- The byte an ANSI-C escape stands for, from the letter after its backslash. -/
private def ansiLetter : UInt8 → Option UInt8
  | 0x61 => some 0x07
  | 0x62 => some 0x08
  | 0x65 => some 0x1B
  | 0x45 => some 0x1B
  | 0x66 => some 0x0C
  | 0x6E => some 0x0A
  | 0x72 => some 0x0D
  | 0x74 => some 0x09
  | 0x76 => some 0x0B
  | 0x5C => some 0x5C
  | 0x27 => some 0x27
  | 0x22 => some 0x22
  | 0x3F => some 0x3F
  | _ => none

/-- Whether a byte is an octal digit. -/
private def octal (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x37

/-- Whether a byte outside quotes would end a shell word, quote or expand it, or is a control
character: what `printf %q` never writes unquoted. -/
private def unquotable (b : UInt8) : Bool :=
  b < 0x20 || b == 0x7F || [0x20, 0x22, 0x24, 0x26, 0x28, 0x29, 0x3C, 0x3E, 0x60, 0x7C].contains b

/-- What follows `cmdline=` in a `C` mark, read, from where its quoting starts, as the one shell
word `printf %q` writes, in bash's style and in zsh's, up to the unquoted `;` that ends it: a
backslash quotes the byte after it, single quotes quote what they hold, and `$'…'` holds escapes,
a letter or three octal digits, each standing for one byte. A byte `%q` never writes unquoted
(`unquotable`), another escape or a quote that does not end stops it. -/
private def wordValue : Quoting → Bytes → Bytes × Stop
  | .bare, [] => ([], .payloadEnd)
  | .bare, 0x3B :: _ => ([], .semicolon)
  | .bare, 0x5C :: b :: rest => (b :: (wordValue .bare rest).1, (wordValue .bare rest).2)
  | .bare, 0x24 :: 0x27 :: rest => wordValue .ansi rest
  | .bare, 0x27 :: rest => wordValue .single rest
  | .bare, b :: rest =>
    if b == 0x5C || unquotable b then ([], .broken)
    else (b :: (wordValue .bare rest).1, (wordValue .bare rest).2)
  | .single, [] => ([], .broken)
  | .single, 0x27 :: rest => wordValue .bare rest
  | .single, b :: rest => (b :: (wordValue .single rest).1, (wordValue .single rest).2)
  | .ansi, [] => ([], .broken)
  | .ansi, 0x27 :: rest => wordValue .bare rest
  | .ansi, 0x5C :: e :: rest =>
    match ansiLetter e with
    | some b => (b :: (wordValue .ansi rest).1, (wordValue .ansi rest).2)
    | none =>
      match rest with
      | d :: o :: tail =>
        if octal e && octal d && octal o then
          (UInt8.ofNat (64 * (e - 0x30).toNat + 8 * (d - 0x30).toNat + (o - 0x30).toNat) ::
              (wordValue .ansi tail).1,
            (wordValue .ansi tail).2)
        else ([], .broken)
      | _ => ([], .broken)
  | .ansi, [0x5C] => ([], .broken)
  | .ansi, b :: rest => (b :: (wordValue .ansi rest).1, (wordValue .ansi rest).2)

/-- A parameter's value as a command line: its bytes, whole when the value ended at a `;`, or
with a payload that is `whole`. -/
private def cmdlineOfValue (whole : Bool) (value : Bytes × Stop) : Cmdline :=
  { bytes := value.1,
    whole :=
      match value.2 with
      | .semicolon => true
      | .payloadEnd => whole
      | .broken => false }

/-- `cmdline_url=`, the parameter that gives a command line as UTF-8 %-escaped text. -/
private def urlParam : Bytes :=
  [0x63, 0x6D, 0x64, 0x6C, 0x69, 0x6E, 0x65, 0x5F, 0x75, 0x72, 0x6C, 0x3D]

/-- `cmdline=`, the parameter that gives a command line quoted as `printf %q` quotes it. -/
private def quotedParam : Bytes := [0x63, 0x6D, 0x64, 0x6C, 0x69, 0x6E, 0x65, 0x3D]

/-- The command line a `C` mark's parameters give, each after a `;`: the first `cmdline_url=`
parameter's value, %-decoded (`urlValue`), or `cmdline=` parameter's, unquoted (`wordValue`);
empty and whole when no parameter gives one. `whole` says whether the payload ended before the
scanner's cap. -/
def cmdlineOf (whole : Bool) : Bytes → Cmdline
  | [] => {}
  | 0x3B :: rest =>
    if urlParam.isPrefixOf rest then cmdlineOfValue whole (urlValue (rest.drop urlParam.length))
    else
      if quotedParam.isPrefixOf rest then
        cmdlineOfValue whole (wordValue .bare (rest.drop quotedParam.length))
      else cmdlineOf whole rest
  | _ :: rest => cmdlineOf whole rest

/-- A number's value from its decimal digits, most significant first. -/
private def decimal (digits : Bytes) : Nat := digits.foldl (fun n d => 10 * n + (d - 0x30).toNat) 0

/-- The exit status a `D` mark's parameters give: the first, when it is a decimal number. -/
def statusOf : Bytes → Option Nat
  | 0x3B :: rest =>
    let field := rest.takeWhile (· != 0x3B)
    if !field.isEmpty && field.all digit then some (decimal field) else none
  | _ => none

/-- The mark an OSC payload is: `133;`, a mark's letter, `A`, `B`, `C` or `D`, then nothing or `;`
and its parameters, which a `C` reads its command line from (`cmdlineOf`) and a `D` its exit
status (`statusOf`). `whole` says whether the payload ended before the scanner's cap. -/
def markOf (payload : Bytes) (whole : Bool) : Option Mark :=
  match payload with
  | 0x31 :: 0x33 :: 0x33 :: 0x3B :: letter :: params =>
    if params.head?.all (· == 0x3B) then
      if letter == 0x41 then some .prompt
      else
        if letter == 0x42 then some .input
        else
          if letter == 0x43 then some (.runs (cmdlineOf whole params))
          else if letter == 0x44 then some (.finished (statusOf params)) else none
    else none
  | _ => none

/-- The mark scanning `b` from `s` completes: the mark an OSC string is, as BEL or ST completes
it, or, past `oscCap`, as the scanner releases it unclassified, from the bytes it held, which are
then not the whole payload. -/
def Scan.mark (s : Scan) (b : UInt8) : Option Mark :=
  match s with
  | .osc rev escSeen =>
    if b == BEL || (escSeen && b == STFinal) then markOf (heldPayload rev) true
    else if rev.length < oscCap then none else markOf (heldPayload (b :: rev)) false
  | _ => none

/-- After feeding a chunk: the terminal, the scanner, client-visible bytes and child replies. -/
structure Result where
  /-- The terminal after every byte of the chunk. -/
  vt : Vt
  /-- The scanner after the chunk, possibly holding an incomplete request. -/
  scan : Scan
  /-- Bytes released to presentation clients, in order. -/
  visible : Bytes
  /-- Replies to owned requests, in order. -/
  replies : Bytes
  /-- Whether the chunk rang the bell or posted a notification (`Scan.hears`). -/
  asks : Bool := false
  /-- The text of the chunk's last notification, if it posted one. -/
  notice : Option Bytes := none
  /-- The shell's marks the chunk completed (`Scan.mark`), in order. -/
  marks : List Mark := []

-- No `deriving Repr`: it would need `Repr Vt`, which the seal withholds because it would
-- publicly read every private field of `VtRec`. Nothing used the instance.

/-- Feed child output byte-by-byte. Per-step output is prepended with a bounded
left append (normally a singleton), so megabyte passthrough remains linear. -/
def feed (v : Vt) (scan : Scan) : Bytes → Result
  | [] => { vt := v, scan, visible := [], replies := [] }
  | b :: bs =>
      let v' := v.step b
      let out := scan.step v' b
      let heard := scan.hears b
      let rest := feed v' out.scan bs
      { vt := rest.vt, scan := rest.scan, visible := out.visible ++ rest.visible,
        replies := out.replies ++ rest.replies, asks := heard.asks || rest.asks,
        notice := rest.notice.or heard.notice, marks := (scan.mark b).toList ++ rest.marks }

end Terminal.Mediation
