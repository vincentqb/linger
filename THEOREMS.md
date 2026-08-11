# Theorems — the tension ledger

Each section names a tension from PLAN.md and the invariant that
resolves it. A theorem lands together with the code it constrains; a
section is listed here before its first proof so the tension is on the
record even while open.

| § | Tension | Invariant | Where |
|---|---------|-----------|-------|
| §Frame | evolvable protocol vs simple daemon | `decode (encode m) = ([m], ∅)`; unknown tag skips exactly its frame | Theorems/Wire.lean |
| §Chunk | TCP/pty chunking is arbitrary vs stateful parsers | decode/feed invariant under concatenation: `feed (a ++ b) = feed b ∘ feed a` | Theorems/Wire.lean, Theorems/Vt.lean |
| §Bound | zellij crashes under cpu/mem load (unbounded actor queues) | every buffer has a structural cap preserved by `step`; nothing to fill | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Total | emulator fed adversarial bytes vs no crashes ever | `Vt.step`/`feed` total (no `partial`, grep-checked); `Good` invariant preserved for any byte: cursor + saved + alt-stashed cursors strictly in bounds, top ≤ bot < rows. (Dims-invariance of `step` is by-construction, not a stated theorem — see SCRATCHPAD step 4.) | Theorems/Vt.lean |
| §Detach | sessions outlive clients (the zmx decoupling) | zero-client session still advances; detach/detach-all don't touch the screen (only permitted effect: a checkpoint) | Theorems/Session.lean |
| §Restore | reboot-resume vs corrupt/stale state files | `load (save s) = some s` (parser state quiesced); `load` total on arbitrary bytes | Theorems/Checkpoint.lean |
| §Name | user-chosen names vs filesystem paths | sanitized names can't escape the socket dir (no `/`, `..`-prefix, NUL, empty) | Theorems/Name.lean |
| §Remote | trusting `ssh host lzmx list` output vs local TUI safety | parser total, garbage-tolerant; §Name carries through; display fields scrubbed of control bytes | Theorems/Remote.lean |
| §Bound(tui) | a picker over a changing list | selection stays inside the filtered matches; query capped | Theorems/Tui.lean |
| §Isolate | many clients on one session vs per-client framing | `.bytes id` leaves every *other* client's record (and decoder) bit-identical | Theorems/Session.lean |
| §Row | a list row's identity vs an unreliable `info` reply | a row's name is a function of the socket filename alone; display fields scrubbed | Theorems/Tui.lean |


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

This is a kernel guarantee, not a theorem — a filesystem property
rather than a property of the pure core. `tests/robust_test.py` pins
it: stale socket plus eight concurrent starts yields exactly one daemon
and one shell, and the name is re-claimable immediately after the owner
exits.

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
* **Grid dimensions are invariant by construction, not by theorem.**
  Every operation preserves `cols`/`rows` syntactically (RIS
  re-derives them through `clampDim`), but the statement is not
  proved; the runtime re-reads dimensions after every feed.
* **§Restore says the codec round-trips, not that the shell's world
  is restored.** A resumed session gets its screen, scrollback, modes,
  labels and cwd back — not its process tree. That is the deliberate
  continuum-shape trade: the work resumes, the programs do not.
