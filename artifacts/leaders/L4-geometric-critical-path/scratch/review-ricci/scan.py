#!/usr/bin/env python3
"""Independent adversarial-review scanner for the three L4-child-ricci-to-doubling modules.

Comment/string-aware stripping, forbidden-token scan, manifold-token scan on the stripped
source, top-level declaration extraction, and headline hypothesis-list comparison between
the frozen hyperbolic theorems and their closed-form counterparts.
"""
import re
import sys
from pathlib import Path

BASE = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/"
            "L4-geometric-critical-path/release/Poincare/L4/Compactness")
FILES = ["RicciToDoubling.lean", "RicciToDoublingHyperbolic.lean",
         "RicciToDoublingHyperbolicClosedForm.lean"]


def strip_lean(src: str) -> str:
    """Remove nested block comments, line comments and string literals (with positions kept
    as spaces so line numbers survive)."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        else:
            if src.startswith("/-", i):
                depth = 1
                out.append("  ")
                i += 2
            elif src.startswith("--", i):
                j = src.find("\n", i)
                j = n if j < 0 else j
                out.append(" " * (j - i))
                i = j
            elif c == '"':
                j = i + 1
                while j < n:
                    if src[j] == "\\":
                        j += 2
                        continue
                    if src[j] == '"':
                        break
                    j += 1
                out.append('"' + " " * (j - i - 1) + ('"' if j < n else ""))
                i = j + 1
            else:
                out.append(c)
                i += 1
    return "".join(out)


FORBIDDEN = ["sorry", "axiom", "admit", "unsafe", "native_decide", "proof_wanted", "sorryAx"]
MANIFOLD_TOKENS = ["Riemannian", "manifold", "geodesic", "coarea", "curvature tensor",
                   "Ricci tensor", "shape operator", "exponential map"]

report = []
stripped = {}
for f in FILES:
    raw = (BASE / f).read_text()
    s = strip_lean(raw)
    stripped[f] = s
    report.append(f"===== {f} =====")
    # forbidden hard-token scan (word boundary)
    for tok in FORBIDDEN:
        hits = [(s[:m.start()].count("\n") + 1, m.group(0))
                for m in re.finditer(r"\b" + re.escape(tok) + r"\b", s)]
        report.append(f"  forbidden {tok!r}: {len(hits)} hit(s) {hits[:5]}")
    # manifold token scan on stripped source
    mhits = []
    for tok in MANIFOLD_TOKENS:
        for m in re.finditer(re.escape(tok), s, flags=re.IGNORECASE):
            mhits.append((s[:m.start()].count("\n") + 1, tok))
    report.append(f"  manifold tokens in stripped source: {len(mhits)} {mhits[:10]}")
    # declaration keyword scan on stripped source
    decls = [(s[:m.start()].count("\n") + 1, m.group(1), m.group(2))
             for m in re.finditer(r"(?m)^\s*(?:noncomputable\s+|private\s+|protected\s+)*"
                                  r"(theorem|def|lemma|axiom|opaque|abbrev)\s+([A-Za-z_][\w'.]*)", s)]
    report.append(f"  top-level decls ({len(decls)}): {decls}")

def extract_hyp_block(fname, thm):
    s = stripped[fname]
    m = re.search(r"(?ms)^theorem\s+" + re.escape(thm) + r"\b(.*?)\n\s*:", s)
    if not m:
        return None
    block = m.group(1)
    # collapse whitespace, drop the theorem-name line residue
    return re.sub(r"\s+", " ", block).strip()

report.append("===== headline hypothesis-list comparison (frozen vs closed form) =====")
pairs = [
    ("hyp_volume_ratio_le_of_ricci_ge", "hyp_volume_ratio_le_of_ricci_ge_closedForm"),
    ("hyp_volume_doubling_of_ricci_ge", "hyp_volume_doubling_closedForm"),
]
for a, b in pairs:
    ba = extract_hyp_block("RicciToDoublingHyperbolic.lean", a)
    bb = extract_hyp_block("RicciToDoublingHyperbolicClosedForm.lean", b)
    report.append(f"  {a} vs {b}: identical={ba == bb}")
    if ba != bb:
        report.append(f"    frozen    : {ba}")
        report.append(f"    closedform: {bb}")

print("\n".join(report))
