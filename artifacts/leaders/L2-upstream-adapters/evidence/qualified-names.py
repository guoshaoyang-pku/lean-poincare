#!/usr/bin/env python3
"""Compute namespace-qualified declaration names for the pinned snapshot.

The static inventories report bare declaration names.  To hand downstream
builders names they can `#check` verbatim (and to drive the compile-time probe
files), this script tracks `namespace`/`end` nesting (and ignores `section`s)
and emits fully qualified names for declarations matching the U1-U12 keywords.

Usage: qualified-names.py <snapshot-root> <out-json>
"""
import json
import re
import sys
from pathlib import Path

from importlib.machinery import SourceFileLoader

HERE = Path(__file__).resolve().parent
inv = SourceFileLoader("inv2", str(HERE / "inventory-v2.py")).load_module()

NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
SECTION_OPEN = re.compile(r"^\s*section\b")
END = re.compile(r"^\s*end\s*([A-Za-z_][A-Za-z0-9_'.]*)?\s*$")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
KW = {
    "U1_curvature": r"(riemann|curvature)",
    "U2_ricci_scalar": r"(ricci|scalarcurvature|scalar_curvature)",
    "U3_geodesic_exp_parallel": r"(geodesic|exponentialmap|expmap|paralleltransport|jacobi|conjugatepoint)",
    "U4_connection": r"(levicivita|covariantderivative|affineconnection)",
    "U6_heat_maxprinciple": r"(heatkernel|heatequation|maximumprinciple|maximum_principle|parabolic)",
    "U7_volume_ibp_bochner": r"(volumeform|divergence|integrationbyparts|bochner)",
    "U8_ricciflow": r"(ricciflow|ishamilt|hamilton)",
    "U9_perelman": r"(reducedlength|reducedvolume|gromovhausdorff|canonicalneighborhood|surgery|entropy|perelman|noncollaps)",
    "U12_monotonicity": r"(monoton|gibbs)",
    "TOPO": r"(fundamentalgroup|simplyconnected|homotopy|covering|homology|triangulation|connectedsum)",
}


def package_of(root: Path, path: Path) -> str:
    rel = path.relative_to(root)
    if rel.parts[0] == "formalized-sources":
        return "/".join(rel.parts[:2])
    return rel.parts[0]


def main():
    root = Path(sys.argv[1]).resolve()
    out = Path(sys.argv[2]).resolve()
    kws = {k: re.compile(v, re.I) for k, v in KW.items()}
    result = {}
    for p in sorted(x for x in root.rglob("*.lean") if ".lake" not in x.parts):
        rel = str(p.relative_to(root))
        pkg = package_of(root, p)
        code = inv.strip_comments(p.read_text(errors="replace"))
        stack = []  # entries: ("ns", name) | ("section",)
        for i, line in enumerate(code.splitlines(), 1):
            m = NS_OPEN.match(line)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            if SECTION_OPEN.match(line):
                stack.append(("section", None))
                continue
            m = END.match(line)
            if m:
                if stack:
                    stack.pop()
                continue
            d = DECL.match(line)
            if not d:
                continue
            kind, name = d.group(1), d.group(2)
            prefix = ".".join(n for t, n in stack if t == "ns")
            fq = f"{prefix}.{name}" if prefix else name
            for k, rx in kws.items():
                if rx.search(name):
                    result.setdefault(k, {}).setdefault(pkg, []).append(
                        {"name": fq, "kind": kind, "file": rel, "line": i})
        # namespace stack sanity: files normally end balanced
    out.write_text(json.dumps(result, indent=1))
    total = sum(len(v) for pkg in result.values() for v in pkg.values())
    print(f"wrote {out}: {total} qualified declarations in {len(result)} keyword groups")
    for k, pkgs in result.items():
        print(f"  {k:26s} " + ", ".join(f"{p.split('/')[-1]}:{len(v)}" for p, v in sorted(pkgs.items())))


if __name__ == "__main__":
    main()
