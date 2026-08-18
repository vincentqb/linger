#!/usr/bin/env python3
"""Coverage of the *code* by the theorems, enforced rather than reviewed.

Two checks, both ratchets. `tests/e2e.sh` runs this and fails on either.

WHY THIS EXISTS, AND WHAT IT REPLACES. The previous gate grepped `Theorems/*.lean`
for each pure-core definition's name and counted the misses. That cannot tell a
claim from a word: `Render.history` — a byte stream the binary writes to the user's
terminal — passed it on the strength of the word "history" appearing in a doc
comment in `Theorems/Session.lean`. Nine of the ten it *did* flag had zero mentions,
so the gate was measuring "is this name absent entirely", not "is anything proved".

Check 1 (`statements`) fixes that by looking only inside theorem **statements** — the
text between `theorem <name>` and the `:=`/`by` that starts the proof. A name that
appears only in a proof, a comment or a section header does not count. This is
strictly stronger than the old gate and it is still a grep-shaped oracle, which is
the right kind for a source-tree property (AGENTS.md, `verifier-in-the-loop`).

Check 2 (`emitters`) is the one that answers "are we proving things about the code
that runs". The runtime's byte-emitting surface is tiny and enumerable: every
`Render.<f>` referenced outside `Zmx/Core/Render.lean` is a stream some code path
actually writes to a terminal. Each must be in EMITTERS below with either a theorem
that constrains it or a stated limitation. A new emitter wired into the runtime fails
the gate until it is classified — which is exactly the failure mode that let the
hand-back ship (a real promise with no anchor, no test and no limitation).

Neither check can be satisfied by writing prose.
"""

import re
import subprocess
import sys
from pathlib import Path


def strip_comments(src: str) -> str:
    """Lean source with `/- … -/` blocks (docstrings included) and `--` line
    comments removed.

    Not cosmetic: it is what makes both checks honest. Without it, check 1 counts a
    definition as claimed when its name appears in a *docstring*, which is the exact
    defect this file replaces — and check 2 reported `Render.rowAnsi`,
    `Render.rowText` and `Render.safeChar` as runtime-emitted because
    `Zmx/Core/Vt.lean` *discusses* them in comments. A gate that reads prose is a
    gate that can be satisfied by writing prose.
    """
    src = re.sub(r"/-.*?-/", " ", src, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", " ", src)

ROOT = Path(__file__).resolve().parent.parent

# ── Check 1 ────────────────────────────────────────────────────────────────────
# Ratchet: pure-core defs named by no theorem *statement*. Only ever goes down
# without discussion; raising it is a deliberate, reviewable edit that says "new
# surface, no claim yet".
#
# `rowSlot` (the row painter's per-cell fold body) was briefly at 22 while its claim
# was pending; `rowAnsi_writes_row` and the `rowSlot_eq_*` equations now name it, so
# it is back to 21. Down to 20 with `size_defaultTabs`, which `restore_tabs_any` needs
# as its ruler-length witness — the ratchet tightens when a claim lands, so it does.
STATEMENT_CAP = 20

# ── Check 2 ────────────────────────────────────────────────────────────────────
# Every byte stream the runtime emits, and what backs it. `theorem` entries must
# also appear in a theorem statement (checked); `limitation` entries must carry a
# reason and are the honest alternative to a silent hole.
EMITTERS = {
    "restore": ("theorem", "restore_grounds / restore_u8_zero / restore_modes_any / "
                           "restore_pen_any / restore_sticky_any / restore_cursor_any / "
                           "restore_grid_any / restore_tabs_any — receiver-quantified for "
                           "the parser, the decoder, the screen cells, the tab ruler and "
                           "every restored field but the title and the DECSC slot"),
    "leaveAnsi": ("theorem", "leave_canonical / leave_canonical_all — parser, modes, "
                             "region, charsets, screen and pen, for any receiver"),
    "utf8s": ("theorem", "utf8s_no_ctl / utf8s_no_esc / utf8s_no_esc_bel / "
                         "Session.utf8s_no_frame — every emitted byte is >= 0x20 and "
                         "not DEL, so no scrubbed text can carry an escape, a BEL, or "
                         "a tab/newline framing byte. Reached from outside Render by "
                         "Session.infoText, which frames listing records with it"),
    "history": ("theorem", "history_framing / history_lines — every byte is a line "
                           "terminator or printable content, and the newline count is "
                           "the row count, so a cell cannot forge a line however the "
                           "session's program filled the grid. Was the last emitter "
                           "assembled through `String` (unprovable: a String does not "
                           "reduce in the kernel); `rowText` now builds List UInt8"),
}


def sh(cmd: str) -> str:
    return subprocess.run(["bash", "-c", cmd], cwd=ROOT, capture_output=True,
                          text=True).stdout


def core_defs() -> list[str]:
    out = sh(r"""grep -h '^\(private \)*def ' Zmx/Core/*.lean \
                 | sed 's/^\(private \)*def \([A-Za-z0-9_.]*\).*/\2/' \
                 | sed 's/.*\.//' | sort -u""")
    return out.split()


def theorem_statements() -> str:
    """The text of every theorem statement in Theorems/, concatenated.

    A statement runs from `theorem <name>` to the `:=` or ` by ` that opens the
    proof. Continuation lines are indented, which is what bounds the scan.
    """
    chunks = []
    for f in sorted((ROOT / "Theorems").glob("*.lean")):
        src = strip_comments(f.read_text())
        for m in re.finditer(
                r"\n(?:private )?theorem\s+([A-Za-z0-9_.']+)"
                r"((?:[^\n]|\n(?=\s))*?)(?::=|\bby\b)", src):
            chunks.append(m.group(2))
    return " ".join(chunks)


def runtime_emitters() -> set[str]:
    """`Render.<f>` referenced anywhere the runtime can reach, i.e. outside the
    module that defines them. `Zmx/Core/Session.lean` counts: it is pure, but it
    is what the daemon calls to build what a client is sent."""
    names: set[str] = set()
    for f in list((ROOT / "Zmx").rglob("*.lean")) + [ROOT / "Main.lean"]:
        if f.name == "Render.lean" and f.parent.name == "Core":
            continue
        if not f.exists():
            continue
        for m in re.finditer(r"Render\.([A-Za-z0-9_]+)", strip_comments(f.read_text())):
            names.add(m.group(1))
    # A *stream* is a def whose result type is `Bytes` or `String`; `safeChar` and
    # friends are helpers inside the construction, not something anyone writes out.
    streams = set()
    for m in re.finditer(r"\ndef ([A-Za-z0-9_]+)[^\n:]*(?:\([^)]*\)\s*)*:\s*(Bytes|String)\b",
                         strip_comments((ROOT / "Zmx/Core/Render.lean").read_text())):
        streams.add(m.group(1))
    return names & streams


def main() -> int:
    fails = []

    # Check 1 — statement-level claim ratchet
    defs = core_defs()
    blob = theorem_statements()
    unclaimed = sorted(d for d in defs
                       if not re.search(r"\b" + re.escape(d) + r"\b", blob))
    print(f"core defs {len(defs)}; named by no theorem STATEMENT: "
          f"{len(unclaimed)} (cap {STATEMENT_CAP})")
    print("  " + " ".join(unclaimed))
    if len(unclaimed) > STATEMENT_CAP:
        fails.append(f"unclaimed core surface grew to {len(unclaimed)} "
                     f"(cap {STATEMENT_CAP}); add a claim or bump the cap deliberately")

    # Check 2 — every runtime-emitted byte stream is classified
    found = runtime_emitters()
    print(f"runtime-emitted byte streams: {' '.join(sorted(found))}")
    for name in sorted(found):
        if name not in EMITTERS:
            fails.append(f"the runtime emits `Render.{name}` and it is in neither the "
                         f"theorem list nor the limitation list of tests/coverage.py — "
                         f"classify it (that unclassified state is what let the "
                         f"hand-back ship)")
            continue
        kind, why = EMITTERS[name]
        if kind == "theorem":
            if not re.search(r"\b" + re.escape(name) + r"\b", blob):
                fails.append(f"`Render.{name}` is listed as theorem-backed but appears "
                             f"in no theorem statement")
            else:
                print(f"  {name}: proved — {why[:60]}…")
        else:
            print(f"  {name}: bounded — {why[:60]}…")
    for name in sorted(EMITTERS):
        if name not in found:
            fails.append(f"tests/coverage.py classifies `Render.{name}` but the runtime "
                         f"no longer emits it — delete the entry so the list stays a "
                         f"description of the code")

    for f in fails:
        print(f"COVERAGE FAIL: {f}", file=sys.stderr)
    print("FAILURES:", len(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
