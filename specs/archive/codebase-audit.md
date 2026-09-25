# 2026-09-25 codebase audit

Status: closed — verified implementation; remote validation blocked by CI billing
Updated: 2026-09-25
Next: no code step remains; request the platform CI run after the closing push
Predecessor: `specs/archive/tmux-resurrect-recipe.md`

## Goal

Audit whether linger's implementation and theorems support its session,
terminal restoration and isolation promises. Fix concrete findings, simplify
unnecessary code, keep the C boundary small, and adopt current compatible Lean
features. Integrate verified steps on `main` and push the result.

## Requirements

- **R1 — Product fidelity.** Preserve the documented command surface, checkpoint
  format, terminal behavior and settled non-goals. Every behavioral fix starts
  with a failing check against the existing implementation.
- **R2 — Useful proofs.** State substantive invariants in `THEOREMS.md` before
  proving them. Each new core definition has an exact constant reference in a
  theorem type. New tests and guarantees are break-verified.
- **R3 — Minimal implementation.** Remove duplication or dead code only where
  no distinct semantics or proof seam requires it. Every deletion passes the
  full verifier stack. Measure C exports and all ratchets from their canonical
  gates; do not duplicate their values here.
- **R4 — Boundaries.** Preserve pure core modules, the sealed VT/session/buffer
  constructors, the isolated raw POSIX interface, frozen poll sets and sanitized
  names. Consider a boundary change only with concrete evidence of improvement.
- **R5 — Lean currency.** Check upstream releases and the matching formatter
  before moving the toolchain. Prefer demonstrated simplifications or stronger
  invariants over unmeasured syntax changes.
- **R6 — Integration.** Independent writers use separate worktrees. The main
  writer owns this spec, `SCRATCHPAD.md`, shared gates and integration. Before
  each step commit run `./lake build` and `./lake build Theorems Tests`; runtime
  edits and deletions also pass foreground `./tests/e2e.sh`. Commit one verified
  checkpoint per step, without rewriting pushed history.

## Steps

0. Establish the clean baseline and record the audit boundaries.
1. Fix runtime/session findings and connect the guarantees to real consumers.
2. Integrate the POSIX/C audit and its regression checks.
3. Integrate VT factoring and invariant improvements.
4. Integrate renderer/checkpoint proof and fidelity improvements.
5. Apply any remaining compatible Lean improvements, review the integrated
   changes, run the full verifier, archive this spec and push.

Steps with no justified implementation change record the negative result.
Additional concrete findings may split a step into smaller verified commits.
The status and completion record below track the actual integration order.

## Completion record

- Step 0: the starting `main` tree was clean at `3ddfb4b`. Both
  `./lake build` and `./lake build Theorems Tests` pass.
- Audit workers: POSIX/C, VT emulator, renderer/checkpoint, and Lean currency.
  Implementation workers have disjoint write scopes in isolated worktrees.
- Main audit: runtime/client/session behavior, proof-to-runtime ties, shared
  verification and final integration.
- Step 1: runtime closes now feed `.closed` into the session machine, and the
  event pump stops after exit. Two real socket/pump regressions failed before
  the fixes and pass afterward. The exact roster-removal theorem rejects a
  reversed client filter. Both required builds and the full foreground verifier
  pass; the pump also no longer requires a partial definition.
- Step 2: one geometry transition now serves attach, attached resize and control
  resize. It emits clamped dimensions that agree with the resulting emulator,
  preserves the full state on repeated effective sizes, and marks real changes
  for persistence. Label edits also mark the checkpoint dirty. Four new
  regressions failed before the fixes; raw-size, lost-dirty and swapped-runtime-
  dimensions mutations fail the new checks. Both required builds and the full
  foreground verifier pass.
- Step 3: malformed traffic and EOF share the last-attacher checkpoint
  transition. Save failure feeds back into the pure machine, retaining dirty
  state for the next periodic attempt. A semantic regression and an injected
  effect-interpreter failure were red before the changes; a lost-dirty mutation
  breaks the new theorem. Both required builds and the full foreground verifier
  pass.
- Step 4: the C signatures now match declarations emitted by the pinned Lean
  compiler. Shared spawn preparation and execution fix closed standard
  descriptors, command lookup and child-environment handling; private raw
  bindings keep NUL and narrowing validation in Lean. Generated-ABI and
  post-fork source checks reject their measured mutations. Every existing C
  export still has a distinct required OS operation. Both required builds and
  the full foreground verifier pass.
- Step 5: ordinary imports can no longer call raw VT mutators; checked
  operations retain their public surface. CSI omitted parameters retain their
  positions, overflow is refused, and vertical absolute positioning respects
  origin mode. General proofs now connect the complete history emitter to its
  budget and establish accepted checkpoint quiescence and exact resaving.
  Explicit dispatch removes the last recursion-depth raise. Semantic and
  public-API mutations fail the new checks. Both required builds and the full
  foreground verifier pass.
- Step 6: the CLI rejects incomplete or malformed info answers without printing
  partial labels or unlinking a connected peer. Remote session names pass the
  proved sanitizer before SSH's shell join. Empty XDG and HOME values use their
  fallback; an explicit LINGER_DIR remains verbatim. The option parser is total,
  removing the runtime's last partial definition. Behavioral and source-gate
  mutations fail the new checks. Both required builds and the full foreground
  verifier pass.
- Step 7: info production and consumption now share one total reply limit.
  Accepted answers preserve every byte across bounded wire frames and end in
  one completion message; an excessive answer emits only a bounded refusal.
  Boundary, truncation and ordering mutations fail the new checks, and source
  gates tie the CLI accumulator to the proved limit. Both required builds and
  the full foreground verifier pass.
- Step 8: VT mode sequences now apply all collected parameters in order.
  Batch composition, single-mode compatibility and structural invariants
  replace proofs that implicitly depended on dropping later parameters.
  Existing receiver-quantified replay guarantees retain their assumptions and
  conclusions. Six behavioral regressions and three restored mutations exercise
  parameter omission, ordering and unintended state changes. Both required
  builds and the full foreground verifier pass.
- Step 9: checkpoint dimensions and declared collection sizes are checked before
  decoding their contents; screen RLE lengths are checked before expansion.
  The new reader is proved extensionally equal to the old accepted-format
  reader, including unread suffixes and noncanonical encodings. Source gates
  catch an expand-before-reject mutation that semantic checks cannot observe.
  Both required builds and the full foreground verifier pass.
- Step 10: monotonic clocks and checkpoint timing use Nat directly. Injected
  UInt64-boundary regressions fail on the old arithmetic; general elapsed-time
  proofs cover early, backward and arbitrarily large ticks. E2E drain uses a
  total loop, and CSI stripping proves input decrease using a library bound.
  Behavioral comparisons and restored mutations preserve helper behavior.
  Source gates tie the Nat clock to the daemon tick. Both required builds and
  the full foreground verifier pass.
- Step 11: reprinting a canonical margin glyph and all its marks is proved to
  change only cursor position and pending wrap, preserving the complete
  remaining terminal state. Reachable narrow/wide witnesses and four rejected
  replay-adapter mutations check that the premises are useful. The ledger
  distinguishes this character-level frame from the pending byte-level
  integration, and its anchor summaries now reflect the existing cursor and
  selected-grid proof scope. Both required builds and source/formatter checks
  pass; this step changes no runtime behavior.
- Step 12: the actual cell-byte emitter now has a margin-cursor theorem that
  needs no receiver grid invariant. Missing cells and saturated combining-mark
  lists preserve the cursor frame, allowing the restoration composition to
  retain its existing receiver scope. Narrow/wide and malformed-grid witnesses,
  together with three rejected adapter mutations, check the statement. Both
  required builds and source/formatter checks pass.
- Step 13: attach captures a bounded replay cursor whose complete walk equals
  the original renderer stream. Exact prefix/suffix, positive-budget progress
  and serialized-storage proofs support incremental delivery. Prior replies,
  replay, live output and exit status retain their order; buffers share one
  allowance, and retired transports have fixed deadlines and count toward
  physical admission. Real regressions and restored mutations exercise large
  paints, exit tails, snapshot capture, ordering, bounds and cleanup. The
  runtime coverage census now catches multiline declarations. Both required
  builds and the full foreground verifier pass, including the new delivery
  suite; the ledger distinguishes logical byte bounds from physical memory
  and conditional draining from network liveness.
- Step 14: a close for the sender or an exit stops the rest of its decoded
  packet. The runtime consumes effect feedback in order before processing the
  next queued event, so transport draining does not extend a detached client's
  authority. The control connection can still detach someone else and continue.
  Original pure and real-socket regressions fail before the fixes; removing
  either guard breaks its theorem, and reversing queue order breaks exactly the
  queued-client cases. Both required builds and the full foreground verifier
  pass.
- Step 15: the cell-byte margin theorem now accepts any initial UTF-8
  accumulator, preserving every other premise and the complete cursor
  conclusion. A separate theorem proves that emitted cell bytes leave no
  partial decoder state. Stale-accumulator and malformed-grid witnesses, plus
  four rejected adapter mutations, check the broader contract without changing
  terminal behavior. Both required builds and source/formatter checks pass.
- Step 16: replay reconstructs deferred wrap in the active, saved and stashed
  cursor slots by reprinting the existing margin glyph and its marks. Complete
  byte-effect equations preserve the remaining state under their explicit
  premises; the old public fidelity endpoints retain their scope, checked by
  an independent frozen probe of 46 contracts. The two internal paint helpers
  now receive canonical repaint context from those unchanged endpoints.
  Resizing clears all three pending flags. Baseline next-glyph checks fail in
  all three slots for narrow and marked wide glyphs; delivered replay now
  matches uninterrupted output. Stage-order, lost-mark and three actual replay
  omission mutations fail their intended checks and pass after restoration.
  Both required builds and the full foreground verifier pass. The ledger
  records decoded-state representability limits and does not claim equivalence
  under arbitrary future terminal input.
- Step 17: final assessment and evidence recorded below, this spec archived,
  and AGENTS.md returned to no live spec. The closing change is documentation
  only; both required builds and source gates pass. Step 16's clean full
  verifier covers the unchanged implementation.

## Final assessment

The architecture still fits the product: one daemon owns one session, a pure
state machine produces effects, and the runtime interprets them. Terminal
composition, an interactive picker and process-tree resurrection remain
outside the product. The audit fixed concrete failures in this architecture
rather than introducing another server or terminal-capability layer.

The theorems support substantive invariants, beyond the exact-constant coverage
census. New results connect accepted checkpoint parsing to exact resaving,
complete history emission to its budget, incremental replay to the complete
captured stream, and real restoration bytes to their cursor and state effects.
Existing receiver-quantified endpoints retain their original scope. Runtime
ordering, cleanup and actual socket delivery have executable checks and source
correspondences because those IO call sites are outside the pure proofs.
The ledger now states the remaining limits instead of treating partial state
equality, logical byte bounds or a passing fixture as a stronger guarantee.

VT factoring is tighter: raw mutators are private, checked transitions form the
public surface, mode parameters share ordered dispatch, and proof stages follow
the emitter's actual dependencies. The isolated `Linger.Posix` / `c/shim.c`
boundary is already the appropriate OS interface. Shared spawn preparation,
Lean validation and a generated-ABI check improve it without another abstraction.
Every retained C export has a measured capability or semantic reason; removing
one would require replacing a distinct required operation.

This is not a net code-size reduction. Between `3ddfb4b` and implementation
checkpoint `f9308ad`, production Lean grew by 428 lines and C by 39 lines,
including comments and layout. The larger growth is in proofs and regression
checks. These changes cover captured streaming, transport retirement, boundary
validation and observed fidelity failures; duplicated paths and unnecessary
partial definitions were removed where they did not carry distinct semantics.
No new C export or external Lean dependency was introduced.

The integer investigation found no general C++ compatibility requirement.
Monotonic timing and internal deadline arithmetic now use Nat directly.
Fixed-width wire values, fd/pid ABI carriers, packed return values and persisted
epoch timestamps keep their representation contracts. Replacing those with Nat
everywhere would still require explicit bounded encoding and OS conversion.

Upstream was rechecked on 2026-09-25: Lean's latest stable release is
`v4.34.1`, but lean-fmt has no matching stable toolchain tag. The repository's
documented paired-upgrade condition therefore retains `v4.34.0-rc2`. The audit
uses that version's module privacy, total do-block loops, String.Slice and
library termination lemmas without raising proof resource allowances.

All accepted worker changes have been integrated on main. Worktrees under
`/tmp/linger-audit-20260925/` retain their frozen handoffs and disposable
evidence; they are not pending feature branches.

## Validation boundary

The local Linux full verifier passes: clean program/proof/test build, source
and layout gates, exact core coverage, generated C ABI, fuzz corpus, POSIX
checks and every live suite. New guarantees have recorded failing baselines
or restored mutation checks. The frozen independent endpoint probe also passes.

GitHub push run
[36174812390](https://github.com/vincentqb/linger/actions/runs/36174812390)
for `f9308ad` failed before any job step ran. Its annotation says recent account
payments failed or the spending limit needs increasing; the platform matrix
was skipped. This is an external validation block, not a test failure or a
macOS pass. The requested manual platform run is the final post-push action.
Billing changes are outside this code audit.
