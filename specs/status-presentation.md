# Consistent status and terminal titles

Status: Linux verified — steps 1–2 complete; publication and cleanup in progress
Updated: 2026-09-29

## Intent

Use one status vocabulary and presentation in `linger ls`, `linger select`,
the compact prompt summary, and attached window titles. Colors use standard
ANSI palette entries (cyan working, yellow unread/unknown, green successful
exit, red failed exit, dim default foreground idle/resumable). Names remain
ordinary text; selection is independent of status color. Preserve useful plain
output when redirected and honor `NO_COLOR`.

`linger status` prints local attention counts, omitting zero counts and
ordinary idle/working/successful/resumable sessions. Unread output, failed
session exits, and unknown sessions remain distinct. The fish recipe invokes
that shell-independent Lean command; it contains no status parsing or policy.
Prompt evaluation samples status when fish redraws the prompt.

Attached titles show the session name, any local attention counts, and the
application's title when present. Sampling is asynchronous and starts the next
attempt one second after completion. Terminal output remains responsive;
title writes wait for a complete control/UTF-8 boundary. Reuse the existing VT
parser rather than introducing a second terminal parser. The title observer
uses a minimal screen and retains no scrollback. One owned command helper
serves both the selector's existing listing and the title's summary sampling.
Malformed sampler output must show unknown status and allow a later sample to
recover without ending the attachment.

Handback clears the title through standard OSC 2 after parser neutralization.
The selector titles itself `linger` on entry and clears its title on exit.
This establishes a default state without a title stack or terminal-specific
capability negotiation. The next shell prompt may set its usual title.

## Steps and ownership

1. Shared presentation and prompt summary. A worker owns status/listing policy,
   picker metadata/presentation, and their proofs and tests. A second worker
   owns the thin fish recipe and its checks. The main writer owns CLI wiring,
   the shared owned-command executor, gates, documentation, and integration.
2. Attached titles and default handback. The main writer owns the title
   observer/composition and client integration, with a worker owning the
   receiver-quantified handback proof and its focused regression checks.
3. Independent review, full verification, compound notes, and cleanup.

Workers write only in separate worktrees. Stage boundaries may be combined
when their shared runtime changes must be verified together; every checkpoint
uses the prescribed build and foreground verifier before commit. All changes
are integrated into main and pushed without rewriting history.

## Verification

New behavior first has a failing check against the predecessor. Kernel proofs
cover common row presentation, palette-only status styles, exact attention
counts, safe title content, and the default handback title. IO source gates
connect proved policy to consumers. Compiling mutations exercise these
oracles. Runtime checks exercise real ptys, complete metadata refresh,
plain/colored output, title updates, split output, responsive cancellation,
and observation without clearing unread state.

Review found a full Unix connection queue could block before the reply deadline.
The new deadline path connects nonblocking and retains unavailable peers as
unknown; a compiling blocking-connect mutation must reproduce the hang and fail
the source gate. The shared VT parser must retain every ESC intermediate until
its final byte and ignore DEL inside pending sequences. Prove those transition
and observer contracts and check their counterexamples. Malformed sampler
stdout and stderr each need a failing live regression before widening the
client's existing error handler.

Run both required Lean builds and the complete foreground Linux verifier,
including generated C ABI, formatting, purity/import boundaries, exact
theorem coverage and reviewed live suite counts. Inspect a rendered selector
frame. A fresh reviewer checks the assembled change. Record actual hosted CI
outcome and any platform limitations, archive this spec, and remove only
integrated clean worker branches/worktrees.

## Verified checkpoint

The assembled foreground verifier passed on 2026-09-29 from 15:32:14Z to
15:39:20Z: clean build, proofs, generated C ABI, source gates, standalone
formatting, theorem/reference coverage, CI runner checks, POSIX smoke tests,
all fourteen live suites with 434 assertions, and the unrelated-session
sentinel. All 158 tracked source identities stayed unchanged during the run.
The required runtime and theorem/test builds also passed before that run.

Independent reviews covered the shared presentation, title observer, parser,
sampler ownership/error handling and source gates. The blocking-connect,
pending-sequence and malformed-output regressions have recorded failing and
passing runs. Source gate mutations compile before rejection, including the
formatter-normalized command-binding cases.

Receipts are indexed in `SCRATCHPAD.md` and
`/tmp/linger-status-20260929/final-verifier/results.json`.
The implementation and dependent proof changes form one verified checkpoint.
Hosted CI and the final worker removal audit remain to be recorded at closure.
