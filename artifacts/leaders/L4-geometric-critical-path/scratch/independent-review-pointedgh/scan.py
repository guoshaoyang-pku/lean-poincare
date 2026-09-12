#!/usr/bin/env python3
"""Independent adversarial scan of the four staged PointedGH modules.

1. comment/string-aware stripping (Lean: -- line, nested /- -/ block, "str", 'char')
2. forbidden constructs in stripped code: sorry, axiom, admit, unsafe, native_decide,
   proof_wanted, partial, sorryAx
3. top-level declaration enumeration vs AxiomAudit coverage
4. statement-only Prop mentions in stripped code
"""
import re
import sys
from pathlib import Path

ROOT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/release")
FILES = [
    ROOT / "Poincare/L4/PointedGH/Transport.lean",
    ROOT / "Poincare/L4/PointedGH/Family.lean",
    ROOT / "Poincare/L4/PointedGH/Instances.lean",
    ROOT / "Poincare/L4/PointedGH/AxiomAudit.lean",
]

FORBIDDEN = ["sorryAx", "sorry", "axiom", "admit", "unsafe", "native_decide",
             "proof_wanted", "partial"]
STMT_ONLY = ["gromovCriterion", "harmonicCoordinatesExistence", "bishopGromovVolumeComparison",
             "curvatureBoundImpliesUniformCovers", "cheegerGromovCompactness",
             "ancientKappaCompactnessFrontier", "canonicalNeighborhoodFrontier"]


def strip_lean(src: str):
    """Return (code_only, comments, strings, line_map) where line_map[i] gives original
    line number of code_only line i (1-based)."""
    out = []          # list of code chars (comments/strings blanked)
    comments = []
    strings = []
    i = 0
    n = len(src)
    block_depth = 0
    while i < n:
        c = src[i]
        if block_depth > 0:
            if src.startswith("/-", i):
                block_depth += 1
                comments.append("-/")
                i += 2
                continue
            if src.startswith("-/", i):
                block_depth -= 1
                i += 2
                continue
            comments.append(c)
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1:
                j = n
            comments.append(src[i:j])
            i = j
            continue
        if src.startswith("/-", i):
            block_depth = 1
            comments.append("/-")
            i += 2
            continue
        if c == '"':
            j = i + 1
            buf = ['"']
            while j < n:
                if src[j] == "\\":
                    buf.append(src[j:j+2])
                    j += 2
                    continue
                buf.append(src[j])
                if src[j] == '"':
                    j += 1
                    break
                j += 1
            s = "".join(buf)
            strings.append(s)
            out.append(" " * len(s))
            i = j
            continue
        if c == "'":
            # char literal or identifier prime; only treat as char if closing quote soon
            j = i + 1
            if j < n and src[j] == "\\":
                j += 2
            else:
                j += 1
            if j < n and src[j] == "'":
                s = src[i:j + 1]
                strings.append(s)
                out.append(" " * len(s))
                i = j + 1
                continue
            out.append(c)
            i += 1
            continue
        out.append(c)
        i += 1
    code = "".join(out)
    return code, comments, strings


# AxiomAudit coverage
audit_src = (ROOT / "Poincare/L4/PointedGH/AxiomAudit.lean").read_text()
audited = set(re.findall(r"#print axioms\s+([A-Za-z0-9_.']+)", audit_src))
print(f"#print axioms entries: {len(audited)}")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|structure|instance|class|opaque)\s+([A-Za-z_«][A-Za-z0-9_«».']*)",
    re.M)

all_decls = {}
for f in FILES:
    src = f.read_text()
    code, comments, strings = strip_lean(src)
    lines = code.split("\n")
    orig_lines = src.split("\n")
    print(f"\n=== {f.name} ===")
    # forbidden scan (code only)
    hits = []
    for tok in FORBIDDEN:
        for m in re.finditer(r"(?<![A-Za-z0-9_'])(" + re.escape(tok) + r")(?![A-Za-z0-9_'])", code):
            ln = code[:m.start()].count("\n") + 1
            hits.append((tok, ln, orig_lines[ln - 1].strip()[:100]))
    if hits:
        for tok, ln, txt in hits:
            print(f"  FORBIDDEN {tok} at line {ln}: {txt}")
    else:
        print("  forbidden-token scan: 0 hits (code only)")
    for tok in STMT_ONLY:
        for m in re.finditer(r"(?<![A-Za-z0-9_'])(" + re.escape(tok) + r")(?![A-Za-z0-9_'])", code):
            ln = code[:m.start()].count("\n") + 1
            print(f"  STMT-ONLY-PROP-MENTION {tok} at line {ln}: {orig_lines[ln-1].strip()[:100]}")
    # declarations
    for m in DECL_RE.finditer(code):
        kind, name = m.group(1), m.group(2)
        if name in ("instance",):
            continue
        ln = code[:m.start()].count("\n") + 1
        full = name
        # namespace context: naive - track "namespace X" occurrences before line
        ns = []
        for lm in re.finditer(r"^\s*namespace\s+([A-Za-z0-9_.«»]+)", code[:m.start()], re.M):
            ns.append(lm.group(1))
        for lm in re.finditer(r"^\s*end\s+([A-Za-z0-9_.«»]+)", code[:m.start()], re.M):
            if ns and ns[-1] == lm.group(1):
                ns.pop()
        full = ".".join(ns + [name]) if ns else name
        all_decls.setdefault(f.name, []).append((kind, full, ln))
        print(f"  {kind:9s} {full}  (line {ln})")

print("\n=== AxiomAudit coverage of Transport.lean + Family.lean declarations ===")
print("(pointed_subseq_of_compact etc. are written unqualified in the audit, so also match suffix)")
missing = []
for fname in ("Transport.lean", "Family.lean"):
    for kind, full, ln in all_decls.get(fname, []):
        short = full.split(".")[-1]
        # namespace fully qualified path for audit: Poincare.L4.PointedGH.<inner path>
        cand = full
        if not cand.startswith("Poincare"):
            cand = "Poincare.L4.PointedGH." + full
        covered = cand in audited or short in {a.split(".")[-1] for a in audited}
        if not covered:
            missing.append((fname, kind, full, ln))
        print(f"  {'OK ' if covered else 'MISS'} {kind:9s} {cand} (line {ln})")
print(f"\nMISSING FROM AUDIT: {missing if missing else 'none'}")
