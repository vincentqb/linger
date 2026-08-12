# Theorems — the tension ledger

Read this file at whichever depth you need:

* **The anchor set** (below) — four theorems that carry the product's
  promises. If you only ever read four statements, read these.
* **The rungs** (the § table) — fourteen tensions from PLAN.md and the
  invariant that resolves each. These are what the anchors are built
  from; a section is listed before its first proof so an open tension is
  on the record.
* The prose sections after that — what the theorems *don't* settle, where
  the model stops, and the two places a guarantee rests on the kernel
  rather than on a proof.

## The anchor set

| Anchor | Statement | Theorem |
|---|---|---|
| **A1. A session survives a crash** | a checkpoint round-trips exactly, and the byte stream rebuilt from it leaves a fresh terminal quiesced — parser in `ground`, no half-decoded character. Any state, no hypotheses | `Resume.resume_quiesced` (§Restore ∘ §Replay) |
| **A2. The daemon cannot be broken by traffic** | no event trace of any length — adversarial clients, hostile pty bytes, any interleaving — breaks a buffer cap, the screen invariant, or one client's isolation from another | `Session.run_wf`, `Session.run_bytes_isolates` (§Bound ∘ §Total ∘ §Isolate) |
| **A3. The transport is invisible** | any re-chunking of any well-formed encoded stream decodes to exactly that stream: same messages, same order, nothing retained, no error | `Wire.decode_encode_chunked` (§Stream = §Frame ∘ §Chunk) |
| **A4. A session name has one owner** | given the kernel grants at most one `flock` holder, at most one daemon ever unlinks or binds a given name | `Claim.at_most_one_owner` (§Claim) |

Each anchor is a *composition* of rungs, which is why the rung table is
still worth having: A1 is §Restore plus §Replay, A2 lifts three §s from
one event to a whole process lifetime, A3 subsumes §Frame and §Chunk as
special cases. The one anchor still incomplete is A1's screen half — the
replayed *cells* equalling the saved cells is carried by
`Tests/Render.lean`'s 14 round-trip fixtures, not yet by proof, and
`Theorems/Resume.lean` says so in the same file as the claim.

## The rungs

| § | Tension | Invariant | Where |
|---|---------|-----------|-------|
| §Frame | evolvable protocol vs simple daemon | `decode (encode m) = ([m], ∅)`; unknown tag skips exactly its frame | Theorems/Wire.lean |
| §Chunk | TCP/pty chunking is arbitrary vs stateful parsers | decode/feed invariant under concatenation: `feed (a ++ b) = feed b ∘ feed a` | Theorems/Wire.lean, Theorems/Vt.lean |
| §Stream | transport fragmentation vs one parsed conversation | any re-chunking of any well-formed encoded stream feeds back to exactly that stream — nothing retained, no error (`decode_encode_chunked`; §Frame and §Chunk are its special cases) | Theorems/Wire.lean |
| §Bound | zellij crashes under cpu/mem load (unbounded actor queues) | every buffer has a structural cap preserved by `step`; nothing to fill | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Total | emulator fed adversarial bytes vs no crashes ever | `Vt.step`/`feed` total (no `partial`, grep-checked); `Good` invariant preserved for any byte: cursor + saved + alt-stashed cursors strictly in bounds, top ≤ bot < rows. Grid dimensions are preserved by every operation too (`dims_feed`; `RIS` re-clamps, which `Good` makes the identity) | Theorems/Vt.lean |
| §Detach | sessions outlive clients (the zmx decoupling) | zero-client session still advances; detach/detach-all don't touch the screen (only permitted effect: a checkpoint) | Theorems/Session.lean |
| §Restore | reboot-resume vs corrupt/stale state files | `load (save s) = some s` (parser state quiesced); `load` total on arbitrary bytes | Theorems/Checkpoint.lean |
| §Name | user-chosen names vs filesystem paths | sanitized names can't escape the socket dir (no `/`, `..`-prefix, NUL, empty); `@` reserved for `name@host` | Theorems/Name.lean |
| §Remote | trusting `ssh host linger ls` output vs local listing safety | parser total, garbage-tolerant; §Name carries through; display fields scrubbed of control bytes | Theorems/Remote.lean |
| §Isolate | many clients on one session vs per-client framing | `.bytes id` leaves every *other* client's record (and decoder) bit-identical | Theorems/Session.lean |
| §Row | a list row's identity vs an unreliable `info` reply | a row's name is the sanitized socket filename alone; the reply can neither change it nor smuggle a second one in | Theorems/Listing.lean |
| §Claim | one session name vs many daemons racing for it | *given* the kernel grants ≤1 `flock` holder, ≤1 daemon ever unlinks or binds that name | Theorems/Claim.lean |
| §Replay | one saved byte stream must recreate the live screen on a fresh terminal | **parser half proved**: a fresh emulator fed a whole restore stream is quiesced — parser in `ground`, no half-decoded character (`restore_quiesced`), for any `Vt` and with no hypotheses. So a reattach can never wedge a client mid-sequence. Cursor placement is proved for the emitted `CUP` sequence (`cup_places_cursor`); the remaining screen/pen *value* fidelity is open, pinned by the decidable `replayEq` + 14 round-trip fixtures | Theorems/Render.lean, Tests/Render.lean |
| §Resume | the product's own promise: crash, reboot, reattach | §Restore ∘ §Replay composed — `load (save c)` succeeds and its replay leaves the terminal quiesced (anchor A1) | Theorems/Resume.lean |


## Reading a row

Each § is proved for *all* inputs, not sampled: the state machines are
`List`/`Nat`-shaped precisely so the inductions go through. Proofs use
`native_decide` nowhere; the unit tests in `Tests/` do, because they
pin concrete behavior (golden bytes, screen contents) where evaluation
is the point.

Each row was **break-verified**: the code was deliberately broken once
to watch the theorem catch it, and the break is recorded in
`SCRATCHPAD.md`. A theorem that survives a wrong definition is worth
nothing.

The machine-layer rows also hold over whole event *traces*, not just
single steps: `run` (Zmx/Core/Session.lean) names the fold the
runtime's poll loop performs, `run_eq_foldl` pins it to that fold
exactly (state threading and effect order), and `run_wf` /
`run_bytes_isolates` (Theorems/Session.lean) lift §Bound + §Total and
§Isolate to the daemon's whole life — no trace of any length breaks
the caps, the screen invariant, or client isolation.

## Why there are ~370 lemmas behind 15 rungs, and how much of it frames retire

Four of the invariance layers — `pstate`, `u8need`, `dims`, `origin`
(`Theorems/Vt.lean`) — are the same ~28 lemmas written four times: for
every emulator operation, "this field is unchanged". About 110 lemmas,
one idea.

The generalization, **demonstrated at the end of `Theorems/Vt.lean`**, is
to state each operation's *frame* — its footprint — once:

```lean
theorem frame_putCell : v.putCell x y c = { v with grid := (v.putCell x y c).grid }
```

Read: *`putCell` writes only `grid`*. Every field invariance is then one
rewrite away, for **any** field — the file shows all four existing layers
falling out of a single `frame_scrollUpIn`, plus `top` and `saved`, which
no layer ever covered. A fifth field would cost nothing.

**How far it goes, measured rather than assumed.** A frame is provable by
`rfl` exactly when the operation's result is a *syntactic record update*.
That holds for the leaf operations — roughly twenty of them (`putCell`,
`moveTo`, `setCol`, the `print*` stages, `enterAlt`/`leaveAlt`,
`eraseRowSpan`, `scrollUpIn`, …) — and those account for the majority of
the 110. It **fails** for two classes, and both failures were spiked
before this claim was written:

* *Compositions.* `frame_print` (the full stage chain) times out: the
  monolithic unfold is too large for a per-branch `rfl`. Gluing staged
  frames instead needs frame *composition*, which needs footprints as
  first-class data (a field-set type, a `WritesWithin` predicate,
  monotonicity) — a small effect system, larger than the sprawl it
  removes.
* *Folds.* `frame_csiDispatch` fails on arms like
  `List.foldl (fun a _ => a.tab) v (range n)`: a fold's result is not a
  record update, so the arm needs an induction (`frame_foldl`) and manual
  gluing — about what the current per-field sweep costs.

So frames retire perhaps 60% of the sprawl cheaply and leave the
composite and fold-based operations roughly as they are. That is still a
net win, and it is a smaller one than "28 replaces 110" would suggest.

Two weaker ideas, recorded because they look attractive and are not:

* *Bundling* the four fields into one conjunction is a 4× win but fixes
  only the fields we happened to need; a frame is complete.
* *Splitting* `Vt` into `{screen, parser, meta}` and typing the printing
  operations `Screen → Screen` does not capture the invariance at all,
  because the read/write distinction is **per-operation**: `print` reads
  `cols`/`rows` to clamp and reads `modes` for wrap/insert while writing
  neither, so any partition that groups `dims` with the cells still
  permits a resize. The refactor that would capture it moves read-only
  data into *parameter* position (`print : Dims → Modes → …`) — far
  larger, and mostly subsumed by frames.

The honest limit of all of them: a frame says what an operation leaves
alone, never what the written fields *become*. Grid fidelity (§Replay
stage 3d) needs the positive specification, which is real content rather
than bookkeeping. Frames retire sprawl; they do not shorten that road.

## Concurrency: what the model rules out, and what the theorems cover

There are **no data races to reason about**, by construction rather
than by proof: the daemon is one process with one `poll` loop, there
are no threads, no `IO.Ref`/`Task`/shared mutable state anywhere, and no
signal handler that touches state (every `signal()` in `c/shim.c` is
`SIG_IGN`/`SIG_DFL`; the client polls `winsizeGet` instead of taking
`SIGWINCH`, which removes async-signal reentrancy as a category). So
"concurrency" here means **interleaving of events from many clients**,
plus **two processes meeting at a file**. Three theorems carry it:

* **§Chunk** — the per-connection half. `poll` hands us whatever bytes
  happen to have arrived, so chunk boundaries are nondeterministic;
  `Decoder.feed_append` says any split of one client's stream yields
  the same messages in the same order. Interleaving cannot desync a
  frame.
* **§Isolate** — the cross-client half. `.bytes id` provably leaves
  every other client's record, including its decoder mid-frame,
  bit-identical. One client cannot corrupt another's framing, and
  §Bound's `decOk` holds for *all* clients simultaneously.
* **§Restore** — the file half. Checkpoints are written tmp+`rename`
  (atomic), and `load` is total on arbitrary bytes, so a reader racing
  a writer sees either the old file or the new one and never dies on a
  torn one.

Two clients typing at once still interleave into the pty — inherent to
a shared terminal, not a defect, and no theorem should claim otherwise.
What *is* deliberately ordered: the pty size is owned by the newest
attached real terminal (`Session.sizeOwner`), so concurrent resizes
converge instead of fighting.

### Session identity at the socket path: closed by the kernel, not by a proof

`Daemon.serve` used to claim a name as probe → unlink-if-refused →
`bind`, and that middle step was a window: with a *stale* socket
present, two starting daemons could both pass the probe, the first
bind, and the second unlink the first's live socket before binding its
own — leaving a daemon alive holding a shell nobody could reach by name.

It now takes an exclusive `flock` on `<name>.lock` **before** the probe
and holds it for the process's whole life, so only the owner may unlink
or bind. `flock` rather than an `O_EXCL`/`mkdir` lock file on purpose:
those are atomic to create but have *no automatic release*, so a
SIGKILLed or power-cut holder leaves a lock nobody can clear, which is
why such designs need a staleness timeout — and any timeout is wrong
(too short steals a live lock, too long makes sessions unstartable
after a reboot). The kernel drops an `flock` when the holder dies, so
there is no timeout in this codebase at all. The lock file is
deliberately never unlinked: unlinking it would let a newcomer lock a
fresh inode while the owner still held the old one.

§Claim states the mutual exclusion this buys, and states it the only
way an OS primitive admits: **conditionally**. `Exclusive` (at most one
`flock` holder) is a hypothesis naming exactly what the kernel is
trusted for; `Guarded` (only the holder unlinks or binds) is ours and is
proved. So the theorem is "≤1 owner per name, given ≤1 lock holder",
and the assumption is one reviewable line rather than an unstated hope.
An advisory lock is still a theorem-grade guarantee over the population
that cooperates — every process claiming a session name is an `linger`
daemon — and §Claim says so precisely, including what it does not
cover.

This is a kernel guarantee plus a proof, not a proof alone.
`tests/robust_test.py` pins the correspondence between §Claim's model
and `serve`: stale socket plus eight concurrent starts yields exactly
one daemon and one shell, and the name is re-claimable immediately
after the owner exits.

## Network filesystems: where the guarantees stop

Three parts of the design assume local storage, in decreasing severity.

**Socket directory (only reachable by setting `LINGER_DIR`).** Unix
sockets are host-local rendezvous names; `bind` on NFS commonly fails
outright, and on a *shared* directory the failure is worse than an
error: sockets belonging to other hosts appear in `list`, no local
listener answers them, and the stale-socket cleanup would delete
another machine's live socket. The defaults avoid this —
`$XDG_RUNTIME_DIR` (tmpfs) or `/tmp/linger-$UID`. Pointing `LINGER_DIR` at
a network mount is unsupported.

**The name lock.** `flock` is unreliable over NFS, so `Exclusive` — and
therefore §Claim — does not hold there. Moot in practice, since the
same shared-directory scenario is already broken by the point above.

**State directory (checkpoints).** This one can arrive by accident: the
default sits under `$HOME`, which is network-mounted on many setups.
Writes are safe (`tmp` + `rename` is atomic, and §Restore's totality
covers a torn or foreign file), but two hosts sharing `$HOME` and each
running a session called `work` would clobber one another's checkpoint.
The default state directory is therefore namespaced by hostname, which
is also the correct semantics: replaying machine B's terminal on
machine A would restore a screen describing a working tree and a
process world that are not there. An explicit `LINGER_DIR` is taken
verbatim — an override is an instruction, not an accident.

Not affected: `readDir` staleness under attribute caching is cosmetic
(a session may appear a beat late), and the daemon's log file has a
single writer. Worth knowing rather than fixing: the `0700` mode on the
socket directory is only as strong as the filesystem enforcing it,
which on NFSv3 with `auth_sys` is not very.

`list` cleaning up stale sockets is *not* part of that hazard: it
unlinks only when `connect` itself fails, which the kernel answers from
the socket's bind state, so a daemon that is merely slow (or SIGSTOPed)
keeps its socket — and §Row keeps it correctly named in the listing.
Verified.

## What these theorems do not settle

* **§Total covers the emulator, not the runtime.** `Zmx/Runtime/*` is
  `IO` with `partial def` loops; its correctness rests on the live
  suites in `tests/`, not on proof. The pure/impure line is the
  `Zmx/Core` boundary, enforced by `tests/e2e.sh`.
* **§Bound bounds our buffers, not the OS's.** A peer that never reads
  eventually fills the kernel socket buffer; the runtime caps its own
  per-client queue at 4 MiB and disconnects rather than grow. That cap
  lives in `Zmx/Runtime/Daemon.lean` and is not proved.
* **Grid dimensions are invariant by theorem now** (`dims_feed`,
  Theorems/Vt.lean): no byte stream changes `cols`/`rows`. `RIS`
  re-derives them through `clampDim`, which is the identity exactly when
  they are already in range — so that one case is conditional on `Good`.
  The runtime still re-reads dimensions after every feed.
* **§Restore says the codec round-trips, not that the shell's world
  is restored.** A resumed session gets its screen, scrollback, modes,
  labels and cwd back — not its process tree. That is the deliberate
  continuum-shape trade: the work resumes, the programs do not.
