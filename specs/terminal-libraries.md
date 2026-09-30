# Reusable terminal libraries

Status: step 1 verified — checkpoint publication and worker cleanup pending
Updated: 2026-09-30

## Intent

The user approves extracting terminal input and including streaming repaint
and safe title emission in the VT toolkit. Keep keyboard decoding independent
of picker bindings, and keep session title composition and output queue policy
outside the toolkit. Preserve linger's commands, selector bindings, paste
protection, title behavior and repaint bytes.

Named Lake targets expose reusable modules; exact import-closure gates enforce
the boundary that Lake's package-wide import path cannot enforce itself.
Use the existing Lean 4.34.1 module interfaces, private representations and
kernel-checked proofs. Add no native code or external dependency.

## Steps

1. Extract decoded input events from selector actions, move generic title
   emission into the terminal module and queue capacity into `Buf`, and expose
   independently buildable library and theorem targets. Preserve the existing
   contracts, add binding and public-import checks, and test the boundaries
   with deliberate compiling mutations. Independently review the integrated
   change, run both required builds and the full foreground verifier, then
   commit and push a verified implementation checkpoint.
2. Verify integration of every worker, preserve their review evidence and
   remove their branches/worktrees. Record actual hosted results, update the
   worklog and status, archive this spec, and commit and push closure.

## Contracts

- Terminal input reports decoded keys rather than selector actions.
- Decoding remains total and bounded; emitted text is printable and valid
  UTF-8. Bracketed paste admits only text and survives incomplete sequences
  and timeouts.
- The picker adapter preserves the current byte bindings and navigation.
  Escape timeout cannot accept or create a session.
- Streaming replay still denotes exactly `Render.restore`; each positive
  budget makes progress while emitting a bounded prefix and retaining its
  exact suffix.
- Generic title payloads exclude control characters, fit the OSC parser cap
  and finish at a parser boundary. Updates wait for a complete parser and
  UTF-8 boundary.
- Session-name sanitization and attention-summary composition stay in linger.
  Queue capacity remains a buffer policy with both frame and front bounds.
- Standalone input and VT targets, including their proofs, import no session,
  manager, POSIX or checkpoint code.

## Verification

The assembled implementation passes both required builds, all four standalone
library/proof targets, ordinary-import API fixtures, the exact-definition
theorem census, source gates and standalone formatter checks.

The full foreground Linux verifier passed on 2026-09-30, 16:37:43Z–16:44:54Z:
clean 172-job build, generated Lean/C ABI, emitter coverage, CI runner and POSIX
checks, and all 437 assertions across fourteen live suites. All 171 source
identities stayed fixed. Original outputs, hashes and independently counted
results are in `/tmp/linger-terminal-libraries-full-20260930-LZgiLX/`.

Independent review accepts the 33-file frozen snapshot with no remaining
findings. Five compiling semantic mutations demonstrate buffer maximality,
title boundary and C1 safety, replay budgets and the original Ctrl-C binding.
Three compiling boundary mutations test the named library roots, the complete
proof import closure and both picker adapter consumers. Every intended check
rejects its mutant; exact restoration and rebuild pass after each experiment.
The handoff and original receipts are in
`/tmp/linger-terminal-libraries-review-aNmyIW/evidence/HANDOFF.md`.

Both agents are closed. Publication, fresh worker cleanup preflight and actual
hosted execution remain for step 2; no hosted pass is claimed.
