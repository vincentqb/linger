module

public import Linger.Core.Render
-- `Vt`'s fields are `private` (the seal, `specs/vt-toolkit.md` Step 1). Terminal is
-- the toolkit's third module and reads cursor/mode state to answer owned queries,
-- so it is a friend by construction, not an escape hatch.
import all Linger.Core.Vt

public section

/-! # Linger.Core.Terminal — bounded child-facing terminal mediation

`Vt` remains the screen model. This module adds the other half of owning a
PTY: recognizing the small documented query profile, replying to the child,
and withholding only those owned requests from presentation clients.
Everything else is emitted byte-for-byte.

Potential CSI/OSC/DCS requests are bounded. Once a sequence is known to be
unowned, passthrough states emit each subsequent byte immediately, so kitty
APC and sixel DCS payloads take constant scanner memory and linear time.
-/

namespace Linger.Core.Terminal

open Linger.Core.Vt Linger.Core.Render

abbrev ESC : UInt8 := 0x1B

abbrev BEL : UInt8 := 0x07

abbrev STFinal : UInt8 := 0x5C

/-- Maximum retained bytes for one possible owned CSI request. -/
def csiCap : Nat := 128

/-- Maximum retained bytes for one possible owned OSC request. -/
def oscCap : Nat := 256

/-- Maximum retained bytes for one possible owned DCS request. -/
def dcsCap : Nat := 2048

/-! ## Exact profile replies -/

def da1Reply : Bytes := [ESC, 0x5B, 0x3F, 0x31, 0x3B, 0x32, 0x63]

def da2Reply : Bytes := [ESC, 0x5B, 0x3E, 0x30, 0x3B, 0x30, 0x3B, 0x30, 0x63]

def statusReply (private_ : Bool) : Bytes :=
  [ESC, 0x5B] ++ (if private_ then [0x3F] else []) ++ [0x30, 0x6E]

def cprRow (v : Vt) : Nat :=
  if v.modes.origin then if v.cursor.y < v.top then 1 else v.cursor.y - v.top + 1
  else v.cursor.y + 1

def cprReply (v : Vt) (private_ : Bool) : Bytes :=
  [ESC, 0x5B] ++ (if private_ then [0x3F] else []) ++ digits (cprRow v) ++ [0x3B] ++
    digits (v.cursor.x + 1) ++
    [0x52]

def versionReply : Bytes :=
  [ESC, 0x50, 0x3E, 0x7C, 0x6C, 0x69, 0x6E, 0x67, 0x65, 0x72, 0x20, 0x30, 0x2E, 0x31, 0x2E, 0x30,
    ESC, STFinal]

def textAreaReply (v : Vt) : Bytes :=
  [ESC, 0x5B, 0x38, 0x3B] ++ digits v.rows ++ [0x3B] ++ digits v.cols ++ [0x74]

/-- Fixed virtual palette reply for OSC 10/11/12. `selector` is the final
ASCII digit and `hex` is `f` for white or `0` for black. -/
def paletteReply (selector hex : UInt8) : Bytes :=
  [ESC, 0x5D, 0x31, selector, 0x3B, 0x72, 0x67, 0x62, 0x3A] ++ List.replicate 4 hex ++ [0x2F] ++
    List.replicate 4 hex ++
    [0x2F] ++
    List.replicate 4 hex ++
    [ESC, STFinal]

/-- The legal XTGETTCAP payload alphabet: hex digits and the `;` that
separates capability names. Everything a well-formed request carries. -/
def capByte (b : UInt8) : Bool :=
  (0x30 ≤ b && b ≤ 0x39) || (0x41 ≤ b && b ≤ 0x46) || (0x61 ≤ b && b ≤ 0x66) || b == 0x3B

/-- XTGETTCAP is answered negatively for every capability, echoing the
requested name so the child knows *which* is unsupported. The echo is
**filtered to the legal alphabet**, because the reply is written into the
child's own input (`Session.onMsg .ptyOut → .writePty`), and a request is
child-controlled output — a `cat` of a hostile file, an ssh stream, a log
tail. A raw payload could carry a CR and a shell command; on a cooked-mode
tty the CR commits a line, so echoing it verbatim let untrusted output run
a command (terminal-reply injection). A conforming request is hex, so the
filter is the identity on it; a malformed one loses exactly the bytes that
could terminate a line. `feed_replies_no_newline` states the guarantee this
buys: no reply linger ever writes to the child contains a line terminator. -/
def xtgetcapReply (payload : Bytes) : Bytes :=
  [ESC, 0x50, 0x30, 0x2B, 0x72] ++ payload.filter capByte ++ [ESC, STFinal]

def decrqssReply : Bytes := [ESC, 0x50, 0x30, 0x24, 0x72, ESC, STFinal]

inductive Decision where
  | unowned
  | owned (reply : Bytes)
  deriving Repr, DecidableEq

/-- Exact CSI rows from the normative profile. No prefix or parameter
normalization is intentional: every unlisted spelling is passthrough. -/
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
                else if seq == [ESC, 0x5B, 0x3F, 0x75] then .owned [] else .unowned

/-- Exact fixed-palette OSC rows. Both BEL and ST terminate requests; replies
always use ST. -/
def classifyOsc (seq : Bytes) : Decision :=
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
      else .unowned

/-! ## Bounded scanner -/

/-- Candidate buffers are reversed, making byte-at-a-time accumulation O(1).
Passthrough states retain no payload. DCS only enters its buffered state after
`+q` or `$q`; sixel (`DCS q`) therefore streams immediately. -/
inductive Scan where
  | ground
  | esc
  | csi (rev : Bytes)
  | csiPass
  | osc (rev : Bytes) (escSeen : Bool)
  | oscPass (escSeen : Bool)
  | dcsIntro
  | dcsKind (kind : UInt8)
  | dcs (kind : UInt8) (payloadRev : Bytes) (escSeen : Bool)
  | strPass (escSeen : Bool)
  deriving Repr, DecidableEq, Inhabited

/-- Bytes retained but not yet sent to presentation clients. -/
def Scan.pending : Scan → Bytes
  | .esc => [ESC]
  | .csi rev => rev.reverse
  | .osc rev _ => rev.reverse
  | .dcsIntro => [ESC, 0x50]
  | .dcsKind kind => [ESC, 0x50, kind]
  | .dcs kind payloadRev escSeen =>
    [ESC, 0x50, kind, 0x71] ++ payloadRev.reverse ++ (if escSeen then [ESC] else [])
  | _ => []

/-- The sole memory invariant stored by `Session.State`. -/
def Scan.Bounded : Scan → Prop
  | .csi rev => rev.length ≤ csiCap
  | .osc rev _ => rev.length ≤ oscCap
  | .dcs kind payloadRev escSeen =>
    ([ESC, 0x50, kind, 0x71] ++ payloadRev.reverse ++ (if escSeen then [ESC] else [])).length ≤
      dcsCap
  | _ => True

structure ScanStep where
  scan : Scan
  visible : Bytes := []
  replies : Bytes := []
  deriving Repr, DecidableEq

/-- Complete one buffered candidate: owned requests disappear from visible
output and produce their one prescribed reply stream; unowned candidates are
released unchanged. -/
def complete (decision : Decision) (seq : Bytes) : ScanStep :=
  match decision with
  | .unowned => { scan := .ground, visible := seq }
  | .owned reply => { scan := .ground, replies := reply }

/-- Advance only the ownership scanner. `v` is the VT state after this byte,
so a CPR samples the cursor at the query's exact stream position. -/
def Scan.step (s : Scan) (v : Vt) (b : UInt8) : ScanStep :=
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
        let next : Scan := .dcs kind nextRev nextEsc
        if next.pending.length ≤ dcsCap then { scan := next }
      else { scan := .strPass nextEsc, visible := s.pending ++ [b] }
  | .strPass escSeen =>
    if escSeen && b == STFinal then { scan := .ground, visible := [b] }
    else { scan := .strPass (b == ESC), visible := [b] }

/-- Flush an incomplete prefix exactly once and reset the scanner. The bytes
have already reached `Vt`, so callers must only broadcast them. -/
def finish (s : Scan) : Bytes × Scan := (s.pending, .ground)

structure Result where
  vt : Vt
  scan : Scan
  visible : Bytes
  replies : Bytes
  deriving Repr

/-- Feed child output byte-by-byte. Per-step output is prepended with a bounded
left append (normally a singleton), so megabyte passthrough remains linear. -/
def feed (v : Vt) (scan : Scan) : Bytes → Result
  | [] => { vt := v, scan, visible := [], replies := [] }
  | b :: bs =>
      let v' := v.step b
      let out := scan.step v' b
      let rest := feed v' out.scan bs
      { vt := rest.vt, scan := rest.scan, visible := out.visible ++ rest.visible,
        replies := out.replies ++ rest.replies }

end Linger.Core.Terminal
