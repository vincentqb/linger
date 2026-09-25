# 2026-09-25 codebase audit

Status: step 0 verified — independent audits and runtime regressions in progress
Updated: 2026-09-25
Next: reproduce runtime close-feedback and geometry findings
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
