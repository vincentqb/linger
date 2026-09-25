# 2026-09-25 codebase audit

Status: step 13 complete — bounded replay and transport draining
Updated: 2026-09-25
Next: finish pending-wrap restoration without weakening existing receiver claims
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
