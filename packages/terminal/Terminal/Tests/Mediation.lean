module

-- The mediator fixtures read cursor and mode state and run compiled under `native_decide`.
import all Terminal.CoreCode.Vt
import all Terminal.CoreCode.Mediation
meta import Terminal.CoreCode.Mediation

/-! # Terminal mediator behavior tests

The theorem layer proves stream laws. These fixtures pin every row of the
normative profile, every possible chunk split, cap overflow, incomplete-prefix
flushes, and graphics passthrough with query-looking payload bytes.
-/

namespace Terminal.Mediation.Tests

open Terminal.Vt Terminal.Render

structure OwnedCase where
  request : Bytes
  reply : Bytes

def profileVt : Vt :=
  { Vt.init 80 24 with
    cursor := { x := 6, y := 8 }, top := 3, bot := 20, modes := { origin := true } }

def ownedCases (v : Vt) : List OwnedCase :=
  [⟨[ESC, 0x5B, 0x63], da1Reply⟩, ⟨[ESC, 0x5B, 0x30, 0x63], da1Reply⟩,
    ⟨[ESC, 0x5B, 0x3E, 0x63], da2Reply⟩, ⟨[ESC, 0x5B, 0x3E, 0x30, 0x63], da2Reply⟩,
    ⟨[ESC, 0x5B, 0x35, 0x6E], statusReply false⟩, ⟨[ESC, 0x5B, 0x3F, 0x35, 0x6E], statusReply true⟩,
    ⟨[ESC, 0x5B, 0x36, 0x6E], cprReply v false⟩, ⟨[ESC, 0x5B, 0x3F, 0x36, 0x6E], cprReply v true⟩,
    ⟨[ESC, 0x5B, 0x3E, 0x71], versionReply⟩, ⟨[ESC, 0x5B, 0x3E, 0x30, 0x71], versionReply⟩,
    ⟨[ESC, 0x5B, 0x31, 0x38, 0x74], textAreaReply v⟩,
    ⟨[ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, BEL], paletteReply 0x30 0x66⟩,
    ⟨[ESC, 0x5D, 0x31, 0x30, 0x3B, 0x3F, ESC, STFinal], paletteReply 0x30 0x66⟩,
    ⟨[ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, BEL], paletteReply 0x31 0x30⟩,
    ⟨[ESC, 0x5D, 0x31, 0x31, 0x3B, 0x3F, ESC, STFinal], paletteReply 0x31 0x30⟩,
    ⟨[ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, BEL], paletteReply 0x32 0x66⟩,
    ⟨[ESC, 0x5D, 0x31, 0x32, 0x3B, 0x3F, ESC, STFinal], paletteReply 0x32 0x66⟩,
    ⟨[ESC, 0x50, 0x2B, 0x71, 0x54, 0x4E, ESC, STFinal], xtgetcapReply [0x54, 0x4E]⟩,
    ⟨[ESC, 0x50, 0x24, 0x71, 0x6D, ESC, STFinal], decrqssReply⟩, ⟨[ESC, 0x5B, 0x3F, 0x75], []⟩,
    ⟨[ESC, 0x5B, 0x32, 0x30, 0x74], []⟩, ⟨[ESC, 0x5B, 0x32, 0x31, 0x74], []⟩,
    ⟨[ESC, 0x5D, 0x35, 0x32, 0x3B, 0x63, 0x3B, 0x3F, ESC, STFinal], []⟩,
    ⟨[ESC, 0x5D, 0x35, 0x32, 0x3B, 0x3B, 0x3F, BEL], []⟩,
    ⟨[ESC, 0x5D, 0x35, 0x32, 0x3B, 0x70, 0x63, 0x3B, 0x3F, BEL], []⟩,
    ⟨[ESC, 0x5D, 0x34, 0x3B, 0x31, 0x3B, 0x3F, BEL], []⟩,
    ⟨[ESC, 0x5D, 0x34, 0x3B, 0x32, 0x35, 0x35, 0x3B, 0x3F, ESC, STFinal], []⟩,
    ⟨[ESC, 0x5D, 0x35, 0x3B, 0x30, 0x3B, 0x3F, BEL], []⟩,
    ⟨[ESC, 0x5D, 0x31, 0x33, 0x3B, 0x3F, BEL], []⟩,
    ⟨[ESC, 0x5D, 0x31, 0x39, 0x3B, 0x3F, ESC, STFinal], []⟩]

/-- XTVERSION reports the same version as `linger --version` and `TERM_PROGRAM_VERSION`. -/
example :
    versionReply =
      [ESC, 0x50, 0x3E, 0x7C] ++ ("linger " ++ versionNumber).toUTF8.toList ++ [ESC, STFinal] := by
  native_decide

def ownedAtSplit (v : Vt) (c : OwnedCase) (i : Nat) : Bool :=
  let a := feed v .ground (c.request.take i)
  let b := feed a.vt a.scan (c.request.drop i)
  a.visible ++ b.visible == [] && a.replies ++ b.replies == c.reply && b.scan == .ground

def ownedAllSplits (v : Vt) (c : OwnedCase) : Bool :=
  (List.range (c.request.length + 1)).all (ownedAtSplit v c)

/-- Every owned grammar row, with both accepted spellings/terminators, emits
its exact reply (or no reply for kitty and for what only a client keeps: the titles, the
clipboard and the colours past the three linger answers) and is absent from presentation
output at every possible chunk boundary. -/
example : (ownedCases profileVt).length = 30 := by native_decide

example : (ownedCases profileVt).all (ownedAllSplits profileVt) = true := by native_decide

/-- CPR samples origin-relative row and one-based column at the query. -/
example : cprReply profileVt false = [ESC, 0x5B, 0x36, 0x3B, 0x37, 0x52] := by native_decide

example : cprReply profileVt true = [ESC, 0x5B, 0x3F, 0x36, 0x3B, 0x37, 0x52] := by native_decide

def passthroughAtSplit (v : Vt) (seq : Bytes) (i : Nat) : Bool :=
  let a := feed v .ground (seq.take i)
  let b := feed a.vt a.scan (seq.drop i)
  a.visible ++ b.visible == seq && a.replies ++ b.replies == [] && b.scan == .ground

def passthroughAllSplits (v : Vt) (seq : Bytes) : Bool :=
  (List.range (seq.length + 1)).all (passthroughAtSplit v seq)

def unknownCsi : Bytes := [ESC, 0x5B, 0x39, 0x39, 0x7A]

def unknownOsc : Bytes := [ESC, 0x5D, 0x32, 0x3B, 0x78, BEL]

/-- A clipboard write, `52 ; c ; aGk=` with ST. -/
def clipboardSet : Bytes :=
  [ESC, 0x5D, 0x35, 0x32, 0x3B, 0x63, 0x3B, 0x61, 0x47, 0x6B, 0x3D, ESC, STFinal]

/-- Requests that look like the owned queries but are not one of their spellings: data other
than `?`, a palette set, a request of two pairs, an empty index and the title stack's push
(`CSI 22 ; 0 t`). -/
def unownedLookalikes : List Bytes :=
  [[ESC, 0x5D, 0x35, 0x32, 0x3B, 0x63, 0x3B, 0x3F, 0x78, BEL],
    [ESC, 0x5D, 0x34, 0x3B, 0x31, 0x3B, 0x72, 0x67, 0x62, 0x3A, 0x66, 0x2F, 0x30, 0x2F, 0x30, BEL],
    [ESC, 0x5D, 0x34, 0x3B, 0x31, 0x3B, 0x3F, 0x3B, 0x32, 0x3B, 0x3F, BEL],
    [ESC, 0x5D, 0x34, 0x3B, 0x3B, 0x3F, BEL], [ESC, 0x5B, 0x32, 0x32, 0x3B, 0x30, 0x74]]

def apcPayload : Bytes := List.replicate 300 0x41 ++ [ESC, 0x5B, 0x63] ++ List.replicate 300 0x42

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

/-- A clipboard write and every look-alike pass through exactly, at every split. -/
example : passthroughAllSplits profileVt clipboardSet = true := by native_decide

example : unownedLookalikes.all (passthroughAllSplits profileVt) = true := by native_decide

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
example : (ownedCases profileVt).all (finishAllProperPrefixes profileVt) = true := by native_decide

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
  [ESC, 0x50, 0x2B, 0x71, 0x35, 0x34, 0x0D, 0x3B, 0x69, 0x64, 0x3E, 0x78, 0x0D, ESC, STFinal]

/-- The hex request round-trips: every legal byte is preserved. -/
example :
    (feed profileVt .ground goodXtget).replies =
      [ESC, 0x50, 0x30, 0x2B, 0x72, 0x35, 0x34, 0x34, 0x65, ESC, STFinal] := by
  native_decide

/-- The malicious request cannot commit a line: the CR and the non-hex i, >, x are gone. -/
example :
    (feed profileVt .ground evilXtget).replies =
      [ESC, 0x50, 0x30, 0x2B, 0x72, 0x35, 0x34, 0x3B, 0x64, ESC, STFinal] := by
  native_decide

/-- Non-vacuity: the raw payload really did contain the injected CR. -/
example : evilXtget.contains 0x0D = true := by native_decide

/-! ### A program that asks for someone

What a chunk hears, split at every byte: a bell rings in ground, after ESC and inside a control
sequence, and nowhere else; the BEL that ends an OSC rings nothing; a notification asks with its
text, ended by BEL or ST; a ConEmu sub-command asks nothing; and a notification past the cap is
heard as the scanner releases it, its text cut to what the scanner held. A notification still
passes through unchanged. -/

/-- Whether the chunk split at `i` asks, and the last notification it posts. -/
def heardAtSplit (v : Vt) (seq : Bytes) (i : Nat) : Bool × Option Bytes :=
  let a := feed v .ground (seq.take i)
  let b := feed a.vt a.scan (seq.drop i)
  (a.asks || b.asks, b.notice.or a.notice)

/-- Whether every split of the chunk hears `expected`. -/
def heardAllSplits (v : Vt) (seq : Bytes) (expected : Bool × Option Bytes) : Bool :=
  (List.range (seq.length + 1)).all fun i => heardAtSplit v seq i == expected

/-- `ESC ] payload` and its terminator, ST when `st`, else BEL. -/
def osc (payload : String) (st : Bool) : Bytes :=
  [ESC, 0x5D] ++ payload.toUTF8.toList ++ (if st then [ESC, STFinal] else [BEL])

example : heardAllSplits profileVt [0x61, BEL, 0x62] (true, none) = true := by native_decide

example : heardAllSplits profileVt [ESC, BEL] (true, none) = true := by native_decide

example : heardAllSplits profileVt [ESC, 0x5B, 0x31, BEL, 0x6D] (true, none) = true := by
  native_decide

example : heardAllSplits profileVt (osc "2;title" false) (false, none) = true := by native_decide

example :
    heardAllSplits profileVt [ESC, 0x5F, 0x61, BEL, 0x62, ESC, STFinal] (false, none) = true := by
  native_decide

example : heardAllSplits profileVt [ESC, 0x50, 0x71, BEL, ESC, STFinal] (false, none) = true := by
  native_decide

example :
    heardAllSplits profileVt (osc "9;edit src/Foo.lean?" false)
        (true, some "edit src/Foo.lean?".toUTF8.toList) =
      true := by
  native_decide

example :
    heardAllSplits profileVt (osc "9;done" true) (true, some "done".toUTF8.toList) = true := by
  native_decide

example : heardAllSplits profileVt (osc "9;4;1;50" false) (false, none) = true := by native_decide

example : heardAllSplits profileVt (osc "9;10;x" true) (false, none) = true := by native_decide

example : heardAllSplits profileVt (osc "9;5" false) (true, some [0x35]) = true := by native_decide

example :
    heardAllSplits profileVt (osc "777;notify;Claude;needs you; now" true)
        (true, some "Claude: needs you; now".toUTF8.toList) =
      true := by
  native_decide

example :
    heardAllSplits profileVt (osc "777;notify;;body" false) (true, some "body".toUTF8.toList) =
      true := by
  native_decide

example : heardAllSplits profileVt (osc "777;other;x" false) (false, none) = true := by
  native_decide

/-- The last of two notifications in a chunk is the one it posts. -/
example :
    heardAllSplits profileVt (osc "9;first" false ++ [0x78] ++ osc "9;second" true)
        (true, some "second".toUTF8.toList) =
      true := by
  native_decide

/-- A notification passes through to clients unchanged. -/
example : passthroughAllSplits profileVt (osc "9;edit src/Foo.lean?" false) = true := by
  native_decide

/-- A notification longer than the scanner holds: `ESC ] 9 ;` and 300 letters. -/
def longNotice : Bytes := osc ("9;" ++ String.ofList (List.replicate 300 'a')) false

/-- It still asks, with the letters the scanner held, `oscCap` bytes less `ESC ] 9 ;` plus the
one byte it released them with, and passes through whole. -/
example :
    heardAllSplits profileVt longNotice (true, some (List.replicate (oscCap - 3) 0x61)) = true := by
  native_decide

example : passthroughWhole profileVt longNotice = true := by native_decide

/-! ### A program's progress

What a chunk reports of its program's progress, split at every byte: ConEmu's `9;4` with each
state from 0 to 4, ended by BEL or ST, with or without a percentage and the `;` an agent's hook
writes after the state; nothing from another state, another `9;` sub-command, a notification or
a title; and the last report of two. A report still passes through unchanged, and it asks
nothing. -/

/-- The progress report the chunk split at `i` completes last. -/
def progressAtSplit (v : Vt) (seq : Bytes) (i : Nat) : Option (Option Progress) :=
  let a := feed v .ground (seq.take i)
  (feed a.vt a.scan (seq.drop i)).progress.or a.progress

/-- Whether every split of the chunk reports `expected`. -/
def progressAllSplits (v : Vt) (seq : Bytes) (expected : Option (Option Progress)) : Bool :=
  (List.range (seq.length + 1)).all fun i => progressAtSplit v seq i == expected

example : progressAllSplits profileVt (osc "9;4;3;" false) (some (some .indeterminate)) = true := by
  native_decide

example : progressAllSplits profileVt (osc "9;4;0;" false) (some none) = true := by native_decide

example : progressAllSplits profileVt (osc "9;4;0" true) (some none) = true := by native_decide

example : progressAllSplits profileVt (osc "9;4;1;50" false) (some (some .normal)) = true := by
  native_decide

example : progressAllSplits profileVt (osc "9;4;2" true) (some (some .error)) = true := by
  native_decide

example : progressAllSplits profileVt (osc "9;4;4;10" false) (some (some .paused)) = true := by
  native_decide

example : progressAllSplits profileVt (osc "9;4;5" false) none = true := by native_decide

example : progressAllSplits profileVt (osc "9;4;33" false) none = true := by native_decide

example : progressAllSplits profileVt (osc "9;4" false) none = true := by native_decide

example : progressAllSplits profileVt (osc "9;10;3" false) none = true := by native_decide

example : progressAllSplits profileVt (osc "9;done" false) none = true := by native_decide

example : progressAllSplits profileVt (osc "2;9;4;3" false) none = true := by native_decide

example :
    progressAllSplits profileVt (osc "9;4;3;" false ++ [0x78] ++ osc "9;4;0;" true) (some none) =
      true := by
  native_decide

/-- A progress report passes through to clients unchanged, and asks nothing. -/
example : passthroughAllSplits profileVt (osc "9;4;3;" false) = true := by native_decide

example : heardAllSplits profileVt (osc "9;4;3;" false) (false, none) = true := by native_decide

/-! ### Lines that enter the history

Whether a chunk adds lines to the history, split at every byte: lines past the bottom of the
screen do, and a line rewritten in place with CR, a title, a cursor move and an erase of the
screen do not; nor does anything on the alternate screen, which keeps no history. -/

/-- Whether the chunk split at `i` adds lines to the history. -/
def linesAtSplit (v : Vt) (seq : Bytes) (i : Nat) : Bool :=
  let a := feed v .ground (seq.take i)
  a.lines || (feed a.vt a.scan (seq.drop i)).lines

/-- Whether every split of the chunk adds lines as `expected` says. -/
def linesAllSplits (v : Vt) (seq : Bytes) (expected : Bool) : Bool :=
  (List.range (seq.length + 1)).all fun i => linesAtSplit v seq i == expected

/-- A terminal two rows tall. -/
def shortVt : Vt := Vt.init 4 2

example : linesAllSplits shortVt [0x61, 0x0D, 0x0A, 0x62, 0x0D, 0x0A, 0x63] true = true := by
  native_decide

example : linesAllSplits shortVt [0x61, 0x0D, 0x0A, 0x62] false = true := by native_decide

example :
    linesAllSplits shortVt ([0x0D, 0x61, 0x0D, 0x62, 0x0D, 0x63] ++ osc "0;spin" false) false =
      true := by
  native_decide

example : linesAllSplits shortVt [ESC, 0x5B, 0x32, 0x4A, ESC, 0x5B, 0x48, 0x78] false = true := by
  native_decide

/-- On the alternate screen, lines past its bottom enter no history. -/
example :
    linesAllSplits (shortVt.feed [ESC, 0x5B, 0x3F, 0x31, 0x30, 0x34, 0x39, 0x68])
        [0x0A, 0x0A, 0x0A, 0x0A] false =
      true := by
  native_decide

/-- A full history still tells each new line: it moves its oldest row out. -/
example : (feed (shortVt.feed (List.replicate (sbCap + 4) 0x0A)) .ground [0x0A]).lines = true := by
  native_decide

/-! ### A shell's marks

What a chunk's marks are, split at every byte: each of `A`, `B`, `C` and `D`, ended by BEL or ST,
with or without parameters; a `C`'s command line from `cmdline_url=`, %-decoded, and from
`cmdline=`, unquoted as bash's and zsh's `printf %q` quote it, as each shell here wrote it; a `D`'s
status when its first parameter is a number; nothing from another letter or another OSC. A value
that stops decoding gives what was read before it, not whole, and a mark past the cap is heard as
the scanner releases it, its command line cut to what the scanner held and not whole. A mark still
passes through unchanged. -/

/-- The marks the chunk split at `i` completes. -/
def marksAtSplit (v : Vt) (seq : Bytes) (i : Nat) : List Mark :=
  let a := feed v .ground (seq.take i)
  a.marks ++ (feed a.vt a.scan (seq.drop i)).marks

/-- Whether every split of the chunk completes `expected`. -/
def marksAllSplits (v : Vt) (seq : Bytes) (expected : List Mark) : Bool :=
  (List.range (seq.length + 1)).all fun i => marksAtSplit v seq i == expected

/-- A command line from its text. -/
def line (text : String) (whole : Bool := true) : Cmdline := { bytes := text.toUTF8.toList, whole }

example : marksAllSplits profileVt (osc "133;A" false) [.prompt] = true := by native_decide

example : marksAllSplits profileVt (osc "133;A;click_events=1" true) [.prompt] = true := by
  native_decide

example : marksAllSplits profileVt (osc "133;B" false) [.input] = true := by native_decide

example : marksAllSplits profileVt (osc "133;C" true) [.runs {}] = true := by native_decide

example :
    marksAllSplits profileVt (osc "133;C;cmdline_url=true" false) [.runs (line "true")] = true := by
  native_decide

/-- fish 4.9's `string escape --style=url`, as it encodes a command line here. -/
example :
    marksAllSplits profileVt
        (osc
          "133;C;cmdline_url=make%20test%3B%20echo%20%24HOME%20%C3%A9%20~/x%20a%2Bb%20100%25%20%22q%22%20%28p%29"
          true)
        [.runs (line "make test; echo $HOME é ~/x a+b 100% \"q\" (p)")] =
      true := by
  native_decide

/-- zsh 5.8's `printf %q` of the same line. -/
example :
    marksAllSplits profileVt
        (osc
          "133;C;cmdline=make\\ test\\;\\ echo\\ \\$HOME\\ é\\ ~/x\\ a+b\\ 100%\\ \\\"q\\\"\\ \\(p\\)"
          false)
        [.runs (line "make test; echo $HOME é ~/x a+b 100% \"q\" (p)")] =
      true := by
  native_decide

/-- bash's `printf %q` of a line with controls, one `$'…'` word, and zsh's, one per character. -/
example :
    marksAllSplits profileVt (osc "133;C;cmdline=$'a\\tb\\nc\\Ed'" true)
          [.runs (line "a\tb\nc\x1bd")] =
        true ∧
      marksAllSplits profileVt (osc "133;C;cmdline=a$'\\t'b$'\\n'c$'\\033'd" false)
          [.runs (line "a\tb\nc\x1bd")] =
        true := by
  native_decide

/-- An empty command line, as `%q` quotes it. -/
example : marksAllSplits profileVt (osc "133;C;cmdline=''" false) [.runs (line "")] = true := by
  native_decide

/-- Parameters before and after the command line. -/
example :
    marksAllSplits profileVt (osc "133;C;cmdline_url=ls;aid=1" false) [.runs (line "ls")] = true ∧
      marksAllSplits profileVt (osc "133;C;aid=1;cmdline=ls" true) [.runs (line "ls")] = true := by
  native_decide

/-- A value that stops decoding gives what was read before it, not whole. -/
example :
    marksAllSplits profileVt (osc "133;C;cmdline_url=make%2" false) [.runs (line "make" false)] =
        true ∧
      marksAllSplits profileVt (osc "133;C;cmdline=make test" false) [.runs (line "make" false)] =
        true ∧
      marksAllSplits profileVt (osc "133;C;cmdline='make" true) [.runs (line "make" false)] =
        true := by
  native_decide

example :
    marksAllSplits profileVt (osc "133;D;0" false) [.finished (some 0)] = true ∧
      marksAllSplits profileVt (osc "133;D" true) [.finished none] = true ∧
      marksAllSplits profileVt (osc "133;D;130;aid=7" false) [.finished (some 130)] = true ∧
      marksAllSplits profileVt (osc "133;D;x" false) [.finished none] = true ∧
      marksAllSplits profileVt (osc "133;D;" false) [.finished none] = true := by
  native_decide

/-- Another letter, a letter followed by more than parameters, another OSC and a notification
are no mark. -/
example :
    marksAllSplits profileVt (osc "133;E" false) [] = true ∧
      marksAllSplits profileVt (osc "133;AB" false) [] = true ∧
      marksAllSplits profileVt (osc "1330;A" false) [] = true ∧
      marksAllSplits profileVt (osc "2;133;A" true) [] = true ∧
      marksAllSplits profileVt (osc "9;133;D;0" false) [] = true := by
  native_decide

/-- A command's marks in one chunk, around its output, in order. -/
example :
    marksAllSplits profileVt
        (osc "133;C;cmdline_url=ls" false ++ "out\r\n".toUTF8.toList ++ osc "133;D;0" true ++
          osc "133;A" false)
        [.runs (line "ls"), .finished (some 0), .prompt] =
      true := by
  native_decide

/-- A mark passes through to clients unchanged. -/
example : passthroughAllSplits profileVt (osc "133;C;cmdline_url=true" false) = true := by
  native_decide

/-- A mark longer than the scanner holds: `ESC ] 133;C;cmdline_url=` and 300 letters. -/
def longMark : Bytes := osc ("133;C;cmdline_url=" ++ String.ofList (List.replicate 300 'a')) false

/-- It is still heard, as the scanner releases it, with the letters the scanner held, `oscCap`
bytes less `ESC ]` and the 18 bytes before the line, plus the one byte it released them with, not
whole; and passes through whole. -/
example :
    marksAllSplits profileVt longMark
        [.runs { bytes := List.replicate (oscCap - 19) 0x61, whole := false }] =
      true := by
  native_decide

example : passthroughWhole profileVt longMark = true := by native_decide

end Terminal.Mediation.Tests
