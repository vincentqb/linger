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
| §Detach | sessions outlive clients (the zmx decoupling) | zero-client session still advances; attach/detach don't touch the grid | Theorems/Session.lean |
| §Restore | reboot-resume vs corrupt/stale state files | `load (save s) = some s`; `load` total on arbitrary bytes | Theorems/Checkpoint.lean |
| §Name | user-chosen names vs filesystem paths | sanitized names can't escape the socket dir (no `/`, `..`, NUL, empty) | Theorems/Name.lean |
| §Remote | trusting `ssh host lzmx list` output vs local TUI safety | parser total, garbage-tolerant (bad line → dropped, never ⊥); §Name carries through | Theorems/Remote.lean |
