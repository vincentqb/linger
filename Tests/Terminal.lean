import Linger.Core.Terminal
/-! # Terminal mediator behavior tests

The theorem layer proves stream laws. These fixtures pin every row of the
normative profile, every possible chunk split, cap overflow, incomplete-prefix
flushes, and graphics passthrough with query-looking payload bytes.
-/

namespace Linger.Core.Terminal.Tests

open Linger.Core.Vt Linger.Core.Render Linger.Core.Terminal

structure OwnedCase where
  request : Bytes
  reply : Bytes


def profileVt : Vt :=
  { Vt.init 80 24 with
    cursor := { x := 6, y := 8 },
    top := 3, bot := 20,
    modes := { origin := true } }


def ownedCases (v : Vt) : List OwnedCase :=
  [ ⟨[ESC, 0x5B, 0x63], da1Reply⟩,
    ⟨[ESC, 0x5B, 0x30, 0x63], da1Reply⟩,
    ⟨[ESC, 0x5B, 0x3E, 0x63], da2Reply⟩,
    ⟨[ESC, 0x5B, 0x3E, 0x30, 0x63], da2Reply⟩,
    ⟨[ESC, 0x5B, 0x35, 0x6E], statusReply false⟩,
    ⟨[ESC, 0x5B, 0x3F, 0x35, 0x6E], statusReply true⟩,
    ⟨[ESC, 0x5B, 0x36, 0x6E], cprReply v false⟩,
    ⟨[ESC, 0x5B, 0x3F, 0x36, 0x6E], cprReply v true⟩,
    ⟨[ESC, 0x5B, 0x3E, 0x71], versionReply⟩,
    ⟨[ESC, 0x5B, 0x3E, 0x30, 0x71], versionReply⟩,
    ⟨[ESC, 0x5B, 0x31, 0x38, 0x74], textAreaReply v⟩,
    ⟨[ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, BEL], paletteReply 0x30 0x66⟩,
    ⟨[ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, ESC, STFinal], paletteReply 0x30 0x66⟩,
    ⟨[ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, BEL], paletteReply 0x31 0x30⟩,
    ⟨[ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, ESC, STFinal], paletteReply 0x31 0x30⟩,
    ⟨[ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, BEL], paletteReply 0x32 0x66⟩,
    ⟨[ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, ESC, STFinal], paletteReply 0x32 0x66⟩,
    ⟨[ESC, 0x50, 0x2B, 0x71, 0x54, 0x4E, ESC, STFinal],
      xtgetcapReply [0x54, 0x4E]⟩,
    ⟨[ESC, 0x50, 0x24, 0x71, 0x6D, ESC, STFinal], decrqssReply⟩,
    ⟨[ESC, 0x5B, 0x3F, 0x75], []⟩ ]


def ownedAtSplit (v : Vt) (c : OwnedCase) (i : Nat) : Bool :=
  let a := feed v .ground (c.request.take i)
  let b := feed a.vt a.scan (c.request.drop i)
  a.visible ++ b.visible == [] &&
    a.replies ++ b.replies == c.reply && b.scan == .ground


def ownedAllSplits (v : Vt) (c : OwnedCase) : Bool :=
  (List.range (c.request.length + 1)).all (ownedAtSplit v c)

/-- Every owned grammar row, with both accepted spellings/terminators, emits
its exact reply (or no reply for kitty) and is absent from presentation output
at every possible chunk boundary. -/
example : (ownedCases profileVt).length = 20 := by native_decide
example : (ownedCases profileVt).all (ownedAllSplits profileVt) = true := by
  native_decide

/-- CPR samples origin-relative row and one-based column at the query. -/
example : cprReply profileVt false =
    [ESC, 0x5B, 0x36, 0x3B, 0x37, 0x52] := by native_decide
example : cprReply profileVt true =
    [ESC, 0x5B, 0x3F, 0x36, 0x3B, 0x37, 0x52] := by native_decide


def passthroughAtSplit (v : Vt) (seq : Bytes) (i : Nat) : Bool :=
  let a := feed v .ground (seq.take i)
  let b := feed a.vt a.scan (seq.drop i)
  a.visible ++ b.visible == seq && a.replies ++ b.replies == [] &&
    b.scan == .ground


def passthroughAllSplits (v : Vt) (seq : Bytes) : Bool :=
  (List.range (seq.length + 1)).all (passthroughAtSplit v seq)


def unknownCsi : Bytes := [ESC, 0x5B, 0x39, 0x39, 0x7A]
def unknownOsc : Bytes := [ESC, 0x5D, 0x32, 0x3B, 0x78, BEL]
def apcPayload : Bytes :=
  List.replicate 300 0x41 ++ [ESC, 0x5B, 0x63] ++ List.replicate 300 0x42
def apc : Bytes := [ESC, 0x5F] ++ apcPayload ++ [ESC, STFinal]
def sixelPayload : Bytes :=
  List.replicate 3000 0x23 ++ [ESC, 0x5B, 0x63] ++ List.replicate 3000 0x7E
def sixel : Bytes := [ESC, 0x50, 0x71] ++ sixelPayload ++ [ESC, STFinal]

def passthroughWhole (v : Vt) (seq : Bytes) : Bool :=
  let r := feed v .ground seq
  r.visible == seq && r.replies == [] && r.scan == .ground

/-- Unknown ANSI and graphics protocols remain exact, including payloads
larger than every candidate cap and bytes that look like an owned query. -/
example : passthroughAllSplits profileVt unknownCsi = true := by native_decide
example : passthroughAllSplits profileVt unknownOsc = true := by native_decide
example : passthroughWhole profileVt apc = true := by native_decide
example : passthroughWhole profileVt sixel = true := by native_decide

/-- A candidate that crosses its cap is released once and remains unowned. -/
def longCsi : Bytes := [ESC, 0x5B] ++ List.replicate csiCap 0x30 ++ [0x7A]
def longOsc : Bytes := [ESC, 0x5D] ++ List.replicate oscCap 0x41 ++ [BEL]
example : passthroughWhole profileVt longCsi = true := by native_decide
example : passthroughWhole profileVt longOsc = true := by native_decide


def finishAtPrefix (v : Vt) (c : OwnedCase) (i : Nat) : Bool :=
  let pref := c.request.take i
  let r := feed v .ground pref
  let flushed := finish r.scan
  r.visible ++ flushed.1 == pref && r.replies == [] && flushed.2 == .ground


def finishAllProperPrefixes (v : Vt) (c : OwnedCase) : Bool :=
  (List.range c.request.length).all (finishAtPrefix v c)

/-- EOF at every incomplete owned-query prefix releases exactly the bytes that
were withheld, emits no reply, and resets the scanner. -/
example : (ownedCases profileVt).all (finishAllProperPrefixes profileVt) = true := by
  native_decide


/-! ### XTGETTCAP echo cannot inject a command

The reply is written into the child's own input, and the request is untrusted
child output, so a raw echo of a payload carrying a CR let a `cat` of a hostile
file run a command (`feed_replies_noNl` is the invariant; these pin the concrete
behavior). A well-formed hex request is echoed unchanged; a malicious one loses
its line terminator. -/

/-- ESC P + q <hex> ESC \ — a genuine capability request, hex-encoded. -/
def goodXtget : Bytes := [ESC, 0x50, 0x2B, 0x71, 0x35, 0x34, 0x34, 0x65, ESC, STFinal]
/-- ESC P + q 5 4 CR ; i d > x CR ESC \ — the payload smuggles a CR and a
command, as a hostile file would. -/
def evilXtget : Bytes :=
  [ESC, 0x50, 0x2B, 0x71, 0x35, 0x34, 0x0D, 0x3B, 0x69, 0x64, 0x3E, 0x78, 0x0D,
   ESC, STFinal]

/-- The hex request round-trips: every legal byte is preserved. -/
example : (feed profileVt .ground goodXtget).replies =
    [ESC, 0x50, 0x30, 0x2B, 0x72, 0x35, 0x34, 0x34, 0x65, ESC, STFinal] := by
  native_decide

/-- The malicious request cannot commit a line: the CR (and the non-hex `i`, `>`,
`x`) are gone; what remains (`54;d`) sits harmlessly in the line buffer. This is
the byte that made it a command injection. -/
example : (feed profileVt .ground evilXtget).replies.contains 0x0D = false := by
  native_decide
example : (feed profileVt .ground evilXtget).replies.contains 0x0A = false := by
  native_decide
/-- Non-vacuity: the raw payload really did contain the injected CR. -/
example : evilXtget.contains 0x0D = true := by native_decide

end Linger.Core.Terminal.Tests
