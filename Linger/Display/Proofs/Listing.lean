module

import all Linger.Display.CoreCode.Listing
import all Linger.Display.CoreCode.Status
-- The proof layer is module-private, so `utf8s_no_ctl` arrives through `import all`.
import all Terminal.Proofs.Render
import all Linger.Display.Proofs.Status
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt.Renderable

/-! # A list row's identity is its socket filename, not the reply

The `info` reply is data from another process (a local
daemon, or — via porcelain — a remote host's `linger`), so it is not
trusted to name itself. `rowFields` derives the row's `name` from the
socket filename alone; these two theorems say the reply can neither
change it (`rowFields_name`) nor smuggle a second one in
(`rowFields_reply_excluded`).
-/

namespace Linger.Display.Listing

/-- The row's `name` is the socket filename for ANY reply, so a peer's
reply can never spoof another session's identity. -/
theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (rowFields socketName info).lookup "name" = some socketName := by simp [rowFields]

/-- Nothing after the leading name — everything the reply contributed —
carries the "name" key: the reply's own name (if any) is physically
dropped, not merely shadowed. -/
theorem rowFields_reply_excluded (socketName v : String) (info : List (String × String)) :
    (⟨"name", v⟩ : String × String) ∉ (rowFields socketName info).tail := by
  simp [rowFields, List.mem_filter]

/-! ## Row identity extends to the status column

Row identity says a reply cannot rename a row. These say it
cannot lie about the row's *health* either: where a row came from, a socket, an end record or
a peer, comes from the caller as its `Row`, never from the reply.
-/

open Linger.Display.Status (Status)

/-- A live socket that did not answer is `unknown`, whatever the reply
contained — so a daemon too busy to answer cannot be reported as idle, and a
crafted reply cannot claim otherwise. -/
theorem rowStatus_unanswered (info : List (String × String)) (h : answered info = false) :
    rowStatus (.live info) = Status.unknown := by
  simp [rowStatus, Linger.Display.Status.classify, h]

/-- No socket, but a checkpoint whose end record does not say how its program ended, is
`resumable`, whatever the reply contained (there is no daemon to have sent one). -/
theorem rowStatus_resumable : rowStatus .stale = Status.resumable := rfl

/-- **An ended session is a result**: a saved row whose end record says its program ended shows
`✓` for status 0 and `✗` for any other, until the first attach shows it or `kill` discards it. -/
theorem rowStatus_ended (status : Nat) :
    rowStatus (.ended status) = if status = 0 then Status.exitedOk else Status.exitedBad := by
  cases status <;> rfl

/-- No socket and an unreadable saved session is `unknown`. -/
theorem rowStatus_gone : rowStatus .broken = Status.unknown := rfl

/-- **A summary that reads records shows what asking would**: a row read from the name's end
record has the status of any answer from its daemon that reports the same `fresh`, `unseen` and
`asks` and no ending. -/
theorem rowStatus_published (fresh unseen asks : Bool) (info : List (String × String))
    (hans : info.any (fun kv => (kv.1 == "pid" || kv.1 == "cmd") && kv.2 != "") = true)
    (hexit : info.lookup "exit" = none) (hfresh : (info.lookup "fresh" == some "true") = fresh)
    (hunseen : (info.lookup "unseen" == some "true") = unseen)
    (hasks : (info.lookup "asks" == some "true") = asks) :
    rowStatus (.published fresh unseen asks) = rowStatus (.live info) := by
  simp [rowStatus, answered, flag, hans, hexit, hfresh, hunseen, hasks]

/-- An empty reply is not an answer, so a busy daemon lists as `unknown`
rather than as a healthy idle session. This is row identity applied to
health: the row still carries its real name, and is honestly marked as one we
could not read. -/
theorem answered_nil : answered [] = false := rfl

/-- A peer cannot claim a state we could not read: an absent or unrecognised
`status` reports `unknown`, not `idle`. This is what keeps a remote glyph an
honest statement rather than an inference from liveness alone. -/
theorem rowStatus_remote_unreadable (junk : String)
    (h : Linger.Display.Status.ofName junk = Status.unknown) :
    rowStatus (.remote true junk) = Status.unknown := by simp [rowStatus, h]

/-- …and a peer that does report one is taken at its word, since it is the
authority on its own session. Round-trips through the porcelain name by
`ofName_name`. -/
theorem rowStatus_remote_reported (st : Status) :
    rowStatus (.remote true (Linger.Display.Status.name st)) = st := by
  simp [rowStatus, Linger.Display.Status.ofName_name]

/-- A session a peer lists as saved shows how its program ended, `✓` or `✗`, as the peer says;
any other status a peer reports for it, it shows as resumable, since only a running session
can be working, idle or waiting. -/
theorem rowStatus_remote_saved (st : Status) :
    rowStatus (.remote false (Linger.Display.Status.name st)) =
      if st = .exitedOk ∨ st = .exitedBad then st else .resumable := by
  cases st <;> rfl

/-- An ended row says how its program ended in the words a client prints when a session ends:
the status of an exit, -/
theorem endingText_exit (code : String) : endingText [("exit", code)] = some s!"status {code}" := by
  simp [endingText]

/-- …the signal that killed it, -/
theorem endingText_signal (code signal : String) :
    endingText [("exit", code), ("signal", signal)] = some s!"killed by signal {signal}" := rfl

/-- …or that linger did not see how it ended, as `Session.outcomeFields` writes each. A row
without these fields, as from a peer, says only that it ended. -/
theorem endingText_unknown (code : String) :
    endingText [("exit", code), ("outcome", "unknown")] = some "outcome unknown" := rfl

/-- A missing or malformed flag reads as `false`, so an omission cannot make
a row look busier or fresher than it is. -/
theorem flag_absent (info : List (String × String)) (k : String) (h : info.lookup k = none) :
    flag info k = false := by simp [flag, h]

/-! ## The width rule

Widths are display columns, as a terminal gives them (`Terminal.Vt.charWidth`): a wide character
takes two, a combining mark none. -/

open Terminal.Vt (charWidth charWidth_low)
open Terminal.Render (textChar)

/-- Making a character printable keeps its width: what it replaces is one column wide, as its
replacement is. -/
theorem charWidth_textChar (c : Char) : charWidth (textChar c) = charWidth c := by
  unfold Terminal.Render.textChar Terminal.Render.safeChar
  split
  · rename_i h
    rw [charWidth_low c
        (by
          simp at h; omega)]
    decide
  · split
    · rename_i h
      rw [charWidth_low c
          (by
            simp at h; omega)]
      decide
    · rfl

theorem cols_nil : cols [] = 0 := rfl

theorem cols_cons (c : Char) (cs : List Char) : cols (c :: cs) = charWidth c + cols cs := by
  simp [cols]

theorem cols_append (a b : List Char) : cols (a ++ b) = cols a + cols b := by simp [cols]

theorem cols_map_textChar (cs : List Char) : cols (cs.map textChar) = cols cs := by
  simp only [cols, List.map_map]
  congr 1
  exact List.map_congr_left fun c _ => charWidth_textChar c

theorem cols_replicate (n : Nat) : cols (List.replicate n ' ') = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, cols_cons, ih]
    have : charWidth ' ' = 1 := by decide
    omega

theorem cols_pad (w : Nat) (cs : List Char) : cols (pad w cs) = cols cs + (w - cols cs) := by
  rw [pad, cols_append, cols_replicate]

theorem cols_prefix {a b : List Char} (h : a <+: b) : cols a ≤ cols b := by
  obtain ⟨t, rfl⟩ := h
  rw [cols_append]
  omega

/-- Dropping trailing blanks keeps a start of the text. -/
theorem dropTrailingBlanks_prefix (cs : List Char) :
    Terminal.Render.dropTrailingBlanks cs <+: cs := by
  unfold Terminal.Render.dropTrailingBlanks
  have h := List.dropWhile_suffix (l := cs.reverse) (· == ' ')
  have := List.reverse_prefix.mpr (by simpa using h)
  simpa using this

/-- What dropping trailing blanks drops is blanks. -/
theorem dropTrailingBlanks_blanks (cs : List Char) :
    ∃ blanks : List Char,
      (∀ c ∈ blanks, c = ' ') ∧ cs = Terminal.Render.dropTrailingBlanks cs ++ blanks := by
  refine ⟨(cs.reverse.takeWhile (· == ' ')).reverse, ?_, ?_⟩
  · intro c hc
    have :=
      List.all_eq_true.mp (List.all_takeWhile (p := (· == ' ')) (l := cs.reverse)) c
        (List.mem_reverse.mp hc)
    simpa using this
  · unfold Terminal.Render.dropTrailingBlanks
    rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]

theorem dropTrailingBlanks_length (cs : List Char) :
    (Terminal.Render.dropTrailingBlanks cs).length ≤ cs.length :=
  (dropTrailingBlanks_prefix cs).length_le

theorem cols_takeCols (room : Nat) (cs : List Char) : cols (takeCols room cs) ≤ room := by
  induction cs generalizing room with
  | nil => simp [takeCols, cols]
  | cons c cs ih =>
    unfold takeCols
    split
    · rw [cols_cons]
      have := ih (room - charWidth c)
      omega
    · simp [cols]

/-- A cut fits its room. -/
theorem cols_cut (room : Nat) (cs : List Char) : cols (cut room cs) ≤ room := by
  unfold cut
  split
  · assumption
  · split
    · simp [cols]
    · rw [cols_append]
      have := cols_prefix (dropTrailingBlanks_prefix (takeCols (room - 1) cs))
      have := cols_takeCols (room - 1) cs
      have : cols ['…'] = 1 := by decide
      omega

theorem mem_takeCols {room : Nat} {cs : List Char} {c : Char} (h : c ∈ takeCols room cs) :
    c ∈ cs := by
  induction cs generalizing room with
  | nil => simp [takeCols] at h
  | cons d ds ih =>
    unfold takeCols at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem d (ih h)
    · simp at h

/-- A cut keeps characters of its text, and adds at most an ellipsis. -/
theorem mem_cut {room : Nat} {cs : List Char} {c : Char} (h : c ∈ cut room cs) :
    c ∈ cs ∨ c = '…' := by
  unfold cut at h
  split at h
  · exact .inl h
  · split at h
    · simp at h
    · rcases List.mem_append.mp h with h | h
      · exact .inl (mem_takeCols ((dropTrailingBlanks_prefix _).subset h))
      · exact .inr (by simpa using h)

/-- What a row shows after its name, before blanks are dropped: the name's padding and the cells,
each in its column, made printable. -/
theorem after_eq (layout : Layout) (info : List (String × String)) :
    ((columns layout info).drop 1).flatten.drop (look info "name").length =
      (List.replicate (layout.nameCol - cols (look info "name").toList) ' ' ++
            (segments layout (project info)).flatten).map
        textChar := by
  simp only [columns, pad, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
    List.flatten_cons, List.map_append, List.append_assoc, ← List.map_flatten]
  rw [List.drop_left' (by simp [String.length])]

/-! ## The human-readable listing is safe to print

The listing goes straight to a terminal, so a control byte in any displayed value — a `cmd`, a
label, a checkpoint filename, a `-r` host — would run as an escape sequence. These say it
cannot, for ANY `info` a reply could carry: the row is rendered through `Render.utf8s`, which
maps every C0/DEL codepoint to U+FFFD, so the guarantee needs no hypothesis about the source.
The `infoText` argument (`Session.infoText_framing`), applied one layer out at the display. -/

open Terminal.Render (utf8s_no_ctl)

/-- **Every byte of a printed row is printable content** — no C0 control, no DEL — whatever the
reply contained. `humanRow` ends in `utf8s`, so this is `utf8s`'s own guarantee. -/
theorem humanRow_printable (layout : Layout) (info : List (String × String)) :
    ∀ b ∈ humanRow layout info, 0x20 ≤ b ∧ b ≠ 0x7F := utf8s_no_ctl _

/-- A row carries no newline, so a `cmd` or label value cannot forge a listing row. -/
theorem humanRow_no_lf (layout : Layout) (info : List (String × String)) :
    ∀ b ∈ humanRow layout info, b ≠ 0x0A := by
  intro b hb he
  have := (humanRow_printable layout info b hb).1
  rw [he] at this; exact absurd this (by decide)

/-- Pieces remove controls before width calculation or styling. A terminal
renderer therefore never clips inside an untrusted escape sequence. -/
theorem piecesOf_printable (width : Option Nat) (name status : String) (after : List Char)
    (printable : ∀ c ∈ after, 32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat)) :
    ∀ piece ∈ piecesOf width name status after,
      ∀ c ∈ piece.text, 32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) := by
  intro piece hp c hc
  simp only [piecesOf, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [List.mem_singleton] at hc
    subst c
    cases Status.ofName status <;> decide
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hc
      have := Terminal.Render.textChar_safe raw
      omega
    · have kept : c ∈ after ∨ c = '…' := by
        split at hc
        · rcases mem_cut hc with h | h
          · exact .inl ((dropTrailingBlanks_prefix after).subset h)
          · exact .inr h
        · exact .inl ((dropTrailingBlanks_prefix after).subset hc)
      rcases kept with h | rfl
      · exact printable c h
      · decide

/-- A row of any width is printable piece by piece. -/
theorem rowPiecesIn_printable (width : Option Nat) (layout : Layout)
    (info : List (String × String)) :
    ∀ piece ∈ rowPiecesIn width layout info,
      ∀ c ∈ piece.text, 32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) := by
  apply piecesOf_printable
  rw [after_eq]
  intro c hc
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hc
  have := Terminal.Render.textChar_safe raw
  omega

/-- The row a listing and the picker share is printable piece by piece. -/
theorem rowPieces_printable (layout : Layout) (info : List (String × String)) :
    ∀ piece ∈ Linger.Display.Listing.rowPieces layout info,
      ∀ c ∈ piece.text, 32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) :=
  rowPiecesIn_printable none layout info

/-- **A printed row, character by character**: the UTF-8 encoding of codepoints that are no
C0 control, DEL or C1 control. `humanRow_printable` is the byte-level half, which an encoded
C1 control satisfies. -/
theorem humanRow_text (layout : Layout) (info : List (String × String)) :
    ∃ cs : List Char,
      humanRow layout info = cs.flatMap Terminal.Render.utf8 ∧
        ∀ c ∈ cs, 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0) := by
  refine
    ⟨((rowPieces layout info).flatMap (·.text)).map Terminal.Render.safeChar, by
      unfold humanRow; exact Terminal.Render.utf8s_eq_flatMap _, ?_⟩
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨piece, hp, hd⟩ := List.mem_flatMap.mp hd
  have h := rowPieces_printable layout info piece hp d hd
  rw [Terminal.Render.safeChar_eq_self (by omega) (by omega)]
  omega

/-- **Every field of a row is clean text**: each character a row of any width shows is
printable, whatever the record holds. -/
theorem rowText_printable (width : Option Nat) (layout : Layout) (info : List (String × String)) :
    ∀ c ∈ rowText width layout info, Linger.Display.Printable c := by
  intro c hc
  obtain ⟨piece, hp, hc⟩ := List.mem_flatMap.mp hc
  have h := rowPiecesIn_printable width layout info piece hp c hc
  simp only [Linger.Display.Printable]
  omega

/-- Exactly the badge is styled; the name, details, labels and watchers are plain. -/
theorem rowPieces_styles (layout : Layout) (info : List (String × String)) :
    (Linger.Display.Listing.rowPieces layout info).map (·.status) =
      [some (Status.ofName ((info.lookup "status").getD "")), none] := rfl

/-- Query emphasis addresses only the name after the body's leading space.
Its length comes from the actual name, independently of padding or metadata. -/
theorem rowPieces_nameSpan (layout : Layout) (info : List (String × String)) :
    (Linger.Display.Listing.rowPieces layout info).map (·.nameSpan) =
      [none, some (1, ((info.lookup "name").getD "").toList.length)] := rfl

/-- A row's two pieces: the styled badge, then the text whose name span is the name's. -/
theorem rowPieces_eq (layout : Layout) (info : List (String × String)) :
    ∃ text,
      Linger.Display.Listing.rowPieces layout info =
        [{ text := [Status.icon (Status.ofName ((info.lookup "status").getD ""))],
           status := some (Status.ofName ((info.lookup "status").getD "")) },
          { text, nameSpan := some (1, ((info.lookup "name").getD "").toList.length) }] := ⟨_, rfl⟩

/-! ## Each field from its one source -/

/-- `filterMap` reads its function only on the list's elements. -/
theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr' fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- Two records that agree on the `sources` fields project to the same record. -/
theorem project_congr {info info' : List (String × String)}
    (h : ∀ key ∈ sources, info.lookup key = info'.lookup key) : project info = project info' := by
  unfold project only
  exact filterMap_congr' fun key hk => by rw [h key hk]

/-- Two records that agree on `keys` keep the same fields of them. -/
theorem only_congr {keys : List String} {info info' : List (String × String)}
    (h : ∀ key ∈ keys, info.lookup key = info'.lookup key) : only keys info = only keys info' := by
  unfold only
  exact filterMap_congr' fun key hk => by rw [h key hk]

/-- **Each cell reads only its own fields**: two records that agree on a cell's fields
(`cellSources`) show the same text in that cell, whatever their other fields say. -/
theorem cells_sources (i : Nat) (info info' : List (String × String))
    (h : ∀ key ∈ cellSources.getD i [], info.lookup key = info'.lookup key) :
    (cells info)[i]? = (cells info')[i]? := by
  match i, h with
  | 0, h =>
    unfold cells; rw [only_congr h]; rfl
  | 1, h =>
    unfold cells; rw [only_congr h]; rfl
  | 2, h =>
    unfold cells; rw [only_congr h]; rfl
  | 3, h =>
    unfold cells; rw [only_congr h]; rfl
  | 4, h =>
    unfold cells; rw [only_congr h]; rfl
  | n + 5, _ => simp [cells]

/-- **Each displayed field comes from its one source**: a row reads only the `sources` fields,
so no other field of a reply, and no label but the description, changes what it shows. -/
theorem rowText_sources (width : Option Nat) (layout : Layout) (info info' : List (String × String))
    (h : ∀ key ∈ sources, info.lookup key = info'.lookup key) :
    rowText width layout info = rowText width layout info' := by
  have hn : look info "name" = look info' "name" := by
    simp only [look, h "name" (by simp [sources])]
  have hs : look info "status" = look info' "status" := by
    simp only [look, h "status" (by simp [sources])]
  have hc : columns layout info = columns layout info' := by
    unfold columns
    rw [hn, hs, project_congr h]
  simp only [rowText, rowPiecesIn, hn, hs, hc]

/-- **The user's words over the program's over the operating system's**: a nonempty description
is the caption; without one, the program's title is; and the foreground program shows only when
the caption does not already name it. -/
theorem caption_precedence (info : List (String × String)) :
    ((info.lookup "title").getD "" ≠ "" → caption info = (info.lookup "title").getD "") ∧
      ((info.lookup "title").getD "" = "" → caption info = (info.lookup "description").getD "") ∧
      (program info = "" ∨ ¬(command (program info)).toList <:+: (caption info).toList) := by
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · simp [caption, look, String.isEmpty_iff, h]
  · simp [caption, look, String.isEmpty_iff, h]
  · unfold program
    split
    · exact .inl rfl
    · rename_i hn
      exact .inr (by simpa using hn)

/-- **The width rule never cuts the glyph or the name**: every row, of any width, starts with
its status glyph, a space and its whole name. -/
theorem rowText_head (width : Option Nat) (layout : Layout) (info : List (String × String)) :
    Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
        ' ' :: ((info.lookup "name").getD "").toList.map Terminal.Render.textChar <+:
      rowText width layout info := by
  simp only [rowText, rowPiecesIn, piecesOf, look, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.map_cons]
  exact ⟨_, rfl⟩

theorem cols_icon (st : Status) : charWidth (Status.icon st) = 1 := by cases st <;> decide

/-- **…and fits the rest within the width**: a row given a width takes no more display columns
than it, unless its glyph and name alone do. -/
theorem rowText_width (width : Nat) (layout : Layout) (info : List (String × String)) :
    cols (rowText (some width) layout info) ≤
      max width (2 + cols ((info.lookup "name").getD "").toList) := by
  simp only [rowText, rowPiecesIn, piecesOf, look, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [cols_append, cols_append, cols_map_textChar, cols_cons, cols_cons, cols_nil, cols_icon]
  have :=
    cols_cut (width - 2 - cols ((info.lookup "name").getD "").toList)
      (Terminal.Render.dropTrailingBlanks
        (((columns layout info).drop 1).flatten.drop ((info.lookup "name").getD "").length))
  have : charWidth ' ' = 1 := by decide
  omega

/-! ## One field, one column -/

theorem segments_cols (layout : Layout) (rest : List (String × String)) :
    (segments layout rest).map (fun part => cols (part.map textChar)) =
      layout.widths.map fun w => if w = 0 then 0 else w + 2 := by
  unfold segments
  rw [List.map_map]
  have hsp : charWidth ' ' = 1 := by decide
  have step :
    ∀ p ∈ layout.widths.zipIdx,
      ((fun part => cols (part.map textChar)) ∘ fun (x : Nat × Nat) =>
            if x.1 = 0 then []
            else ' ' :: pad x.1 (cut x.1 ((cells rest).getD x.2 "").toList) ++ [' '])
          p =
        (fun w => if w = 0 then 0 else w + 2) p.1 := by
    intro p _
    simp only [Function.comp]
    split
    · rfl
    · rw [cols_map_textChar, List.cons_append, cols_cons, cols_append, cols_pad, cols_cons,
        cols_nil]
      have := cols_cut p.1 ((cells rest).getD p.2 "").toList
      omega
  rw [List.map_congr_left step]
  have :=
    congrArg (List.map fun w => if w = 0 then 0 else w + 2) (List.zipIdx_map_fst 0 layout.widths)
  rw [List.map_map] at this
  exact this

/-- **Each field starts at its column's offset**: a row's parts are its text and then blanks, and,
while its name fits the name column, each part takes the display columns its layout gives it, so
each field starts at the same column in every row of a view. -/
theorem columns_aligned (layout : Layout) (info : List (String × String)) :
    (∃ blanks : List Char,
        (∀ c ∈ blanks, c = ' ') ∧
          (columns layout info).flatten = rowText none layout info ++ blanks) ∧
      (cols ((info.lookup "name").getD "").toList ≤ layout.nameCol →
        (columns layout info).map cols = layout.spans) := by
  constructor
  · obtain ⟨blanks, hb, hsplit⟩ :=
      dropTrailingBlanks_blanks
        (((columns layout info).drop 1).flatten.drop (look info "name").length)
    refine ⟨blanks, hb, ?_⟩
    have htc : textChar ' ' = ' ' := by decide
    have hname :
      ((columns layout info).drop 1).flatten.take (look info "name").length =
        (look info "name").toList.map textChar := by
      simp only [columns, pad, List.cons_append, List.nil_append, List.drop_succ_cons,
        List.drop_zero, List.flatten_cons, List.map_append, List.append_assoc]
      rw [List.take_left' (by simp [String.length])]
    have whole :
      (columns layout info).flatten =
        Status.icon (Status.ofName (look info "status")) ::
          ' ' :: ((columns layout info).drop 1).flatten := by
      simp [columns]
    rw [whole, ←
      List.take_append_drop (look info "name").length ((columns layout info).drop 1).flatten, hname,
      hsplit]
    simp [rowText, rowPiecesIn, piecesOf, htc]
  · intro hname
    simp only [columns, List.map_append, List.map_cons, List.map_nil, Layout.spans]
    rw [List.map_map]
    have := segments_cols layout (project info)
    simp only [Function.comp_def] at this ⊢
    rw [this]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩
    · rw [cols_cons, cols_cons, cols_nil, cols_icon]
      decide
    · rw [cols_map_textChar, cols_pad]
      simp only [look] at hname ⊢
      omega

/-- Removing style produces exactly the bytes of the same plain row pieces. -/
theorem renderPieces_plain (pieces : List RowPiece) :
    Linger.Display.Listing.renderPieces false pieces =
      Terminal.Render.utf8s (pieces.flatMap (·.text)) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
    cases hs : piece.status <;> simp_all [renderPieces, Terminal.Render.utf8s, List.flatMap_append]

/-- Uncoloured terminal output is exactly the plain rows: one row per session over the shared
name column, within the width when one is given, each LF-terminated, or the empty-state line. -/
theorem terminalListing_plain (width : Option Nat) (rows : List (List (String × String))) :
    Linger.Display.Listing.terminalListing false width rows =
      if rows.isEmpty then Terminal.Render.utf8s "no sessions".toList ++ [0x0A]
      else
        rows.flatMap
          (fun r =>
            Terminal.Render.utf8s (rowText width (layoutOf rows width.isSome) r) ++ [0x0A]) := by
  simp [terminalListing]

/-- **Every byte of the whole uncoloured listing is printable content or a row-terminating
newline** — the only bytes are what the rows render and the `0x0A` separators. -/
theorem terminalListing_plain_printable (width : Option Nat)
    (rows : List (List (String × String))) :
    ∀ b ∈ terminalListing false width rows, (0x20 ≤ b ∧ b ≠ 0x7F) ∨ b = 0x0A := by
  intro b hb
  rw [terminalListing_plain] at hb
  by_cases hz : rows.isEmpty
  · rw [ite_eq_left hz] at hb
    rcases List.mem_append.mp hb with h | h
    · exact Or.inl (utf8s_no_ctl _ b h)
    · exact Or.inr (by simpa using h)
  · rw [ite_eq_right hz] at hb
    rw [List.mem_flatMap] at hb
    obtain ⟨r, -, hbr⟩ := hb
    rcases List.mem_append.mp hbr with h | h
    · exact Or.inl (utf8s_no_ctl _ b h)
    · exact Or.inr (by simpa using h)

end Linger.Display.Listing
