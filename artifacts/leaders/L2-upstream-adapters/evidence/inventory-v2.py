#!/usr/bin/env python3
"""Comment-aware API inventory for the pinned Frenzymath snapshot (pass 2).

Pass 1 (`inventory-upstream.py`) matched markers anywhere on a line, so
docstring prose such as "this is not an axiom" produced false positives.  Pass 2
strips Lean line comments, nested block comments and string literals before
matching, and additionally extracts declarations whose names match the
problem keywords of the local critical path (blockers U1-U12).

Usage: inventory-v2.py <snapshot-root> <out-json> [<out-md>]
"""
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
MARKERS = {
    "sorry": re.compile(r"\bsorry\b"),
    "axiom_decl": re.compile(r"^\s*axiom\s", re.M),
    "admit": re.compile(r"\badmit\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "proof_wanted": re.compile(r"\bproof_wanted\b"),
}
KEYWORDS = {
    "U1_curvature_tensor": r"(riemann|curvaturetensor|curvature_tensor|riemanntensor|sectional|curvature)",
    "U2_ricci_scalar": r"(ricci|scalarcurvature|scalar_curvature)",
    "U3_geodesic_exp_parallel": r"(geodesic|exponentialmap|expmap|\bexp\b|paralleltransport|parallel_transport|jacobi|conjugatepoint)",
    "U4_levi_civita_connection": r"(levicivita|levi_civita|connection|covariantderivative|covariant_derivative)",
    "U5_germ_tensoriality": r"(germ|tensorial|tensorfield|tensor_field)",
    "U6_heat_parabolic": r"(heatkernel|heat_kernel|heatequation|heat_equation|parabolic|maximumprinciple|maximum_principle)",
    "U7_volume_form_ibp_bochner": r"(volumeform|volume_form|divergence|integrationbyparts|integration_by_parts|bochner|laplacian|laplace)",
    "U8_ricci_flow_existence": r"(ricciflow|ricci_flow|hamilton|shorttime|short_time)",
    "U9_perelman_machinery": r"(reducedlength|reducedvolume|gromovhausdorff|gromov_hausdorff|canonicalneighborhood|canonical_neighborhood|surgery|neck|entropy|perelman|noncollaps|kappa)",
    "U10_tensor_laplacian": r"(tensorlaplacian|tensor_laplacian|diffusion)",
    "U11_orientability": r"(orientab|orientation)",
    "U12_FW_mu_monotonicity": r"(monoton|functional|\bmu\b|\bW\b|gibbs|conjugateheat|conjugate_heat)",
    "TOPO_recognition": r"(fundamentalgroup|fundamental_group|simplyconnected|simply_connected|homotopy|covering|homology|sphere|threemanifold|three_manifold|triangulation|connectedsum|connected_sum|poincare)",
    "METRIC_length_hopfrinow": r"(lengthspace|length_space|hopfrinow|hopf_rinow|injectivityradius|injectivity_radius|metriccompletion)",
}


def strip_comments(text: str) -> str:
    """Blank out Lean line comments, nested block comments and string bodies.

    Newlines are preserved so line numbers stay valid.  This is a scanner, not a
    parser: interpolation inside `s!"..."` is blanked along with the string.
    """
    out = []
    i, n = 0, len(text)
    depth = 0
    in_str = False
    in_line = False
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if in_str:
            if c == "\\":
                out.append("  ")
                i += 2
                continue
            if c == '"':
                in_str = False
                out.append('"')
                i += 1
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if c == "-" and nxt == "-":
            in_line = True
            out.append("  ")
            i += 2
            continue
        if c == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if c == '"':
            in_str = True
            out.append('"')
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def package_of(root: Path, path: Path) -> str:
    rel = path.relative_to(root)
    if rel.parts[0] == "formalized-sources":
        return "/".join(rel.parts[:2])
    return rel.parts[0]


def main():
    root = Path(sys.argv[1]).resolve()
    out_json = Path(sys.argv[2]).resolve()
    out_md = Path(sys.argv[3]).resolve() if len(sys.argv) > 3 else None
    files = sorted(p for p in root.rglob("*.lean") if ".lake" not in p.parts)
    kws = {k: re.compile(v, re.I) for k, v in KEYWORDS.items()}
    pkgs = defaultdict(lambda: {
        "files": 0, "lines": 0, "decls": 0,
        "markers": Counter(), "marker_hits": defaultdict(list),
        "keywords": defaultdict(list), "namespaces": set(),
    })
    decl_index = []
    for p in files:
        rel = str(p.relative_to(root))
        pkg = package_of(root, p)
        text = p.read_text(errors="replace")
        code = strip_comments(text)
        lines = code.splitlines()
        P = pkgs[pkg]
        P["files"] += 1
        P["lines"] += len(text.splitlines())
        declared_here = []
        for i, line in enumerate(lines, 1):
            m = DECL.match(line)
            if m:
                P["decls"] += 1
                name = m.group(2)
                declared_here.append((m.group(1), name, i, line.strip()))
                for k, rx in kws.items():
                    if rx.search(name):
                        P["keywords"][k].append({"name": name, "kind": m.group(1),
                                                 "file": rel, "line": i})
        for k, rx in MARKERS.items():
            hits = [i for i, line in enumerate(lines, 1) if rx.search(line)]
            if hits:
                P["markers"][k] += len(hits)
                P["marker_hits"][k].extend({"file": rel, "line": i} for i in hits[:40])
        for kind, name, i, src in declared_here:
            decl_index.append({"package": pkg, "kind": kind, "name": name,
                               "file": rel, "line": i})
        for ns in re.findall(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", code, re.M):
            P["namespaces"].add(ns)

    summary = {}
    for pkg, P in sorted(pkgs.items()):
        summary[pkg] = {
            "files": P["files"], "lines": P["lines"], "decls": P["decls"],
            "markers": dict(P["markers"]),
            "marker_hits": {k: v[:10] for k, v in P["marker_hits"].items()},
            "keywords": {k: v[:60] for k, v in sorted(P["keywords"].items())},
            "keyword_counts": {k: len(v) for k, v in sorted(P["keywords"].items())},
            "namespaces": sorted(P["namespaces"])[:50],
        }
    doc = {"root": str(root), "lean_files": len(files),
           "packages": summary, "declaration_index_size": len(decl_index)}
    out_json.write_text(json.dumps(doc, indent=1))

    if out_md:
        lines = ["# Frenzymath snapshot API inventory (comment-aware)", "",
                 f"Root: `{root}`", f"Lean files: {len(files)}", "",
                 "## Marker counts (comments stripped)", "",
                 "| package | files | lines | decls | sorry | axiom | admit | unsafe | native_decide | proof_wanted |",
                 "|---|---|---|---|---|---|---|---|---|---|"]
        for pkg, s in summary.items():
            m = s["markers"]
            lines.append("| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |".format(
                pkg, s["files"], s["lines"], s["decls"], m.get("sorry", 0),
                m.get("axiom_decl", 0), m.get("admit", 0), m.get("unsafe", 0),
                m.get("native_decide", 0), m.get("proof_wanted", 0)))
        lines += ["", "## Keyword hits by blocker", ""]
        for kw in KEYWORDS:
            lines.append(f"### {kw}")
            lines.append("")
            for pkg, s in summary.items():
                hits = s["keywords"].get(kw, [])
                if hits:
                    names = ", ".join(sorted({h["name"] for h in hits})[:25])
                    lines.append(f"- **{pkg}** ({len(hits)}): {names}")
            lines.append("")
        out_md.write_text("\n".join(lines))
    print(json.dumps({p: {"files": s["files"], "decls": s["decls"],
                          "markers": s["markers"],
                          "keyword_counts": s["keyword_counts"]}
                      for p, s in summary.items()}, indent=1))


if __name__ == "__main__":
    main()
