#!/usr/bin/env python3
"""Static API/claim inventory of the pinned Frenzymath snapshot.

Reads every tracked `.lean` file below `third_party/frenzymath/Poincare-Conjecture`
(excluding build caches) and records, per package:

* file/line counts,
* declaration counts by kind,
* occurrences of the forbidden / audit-relevant markers
  (`sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`),
* module roots and top-level namespaces.

The output is deliberately textual/static: it is an inventory to drive the
compiled audit, not itself proof evidence.

Usage: inventory-upstream.py <snapshot-root> <output-json>
"""
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|example)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
DECL_KIND_ONLY = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
MARKERS = {
    "sorry": re.compile(r"\bsorry\b"),
    "axiom_decl": re.compile(r"^\s*axiom\b"),
    "admit": re.compile(r"\badmit\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "proof_wanted": re.compile(r"\bproof_wanted\b"),
    "implemented_by": re.compile(r"@\[\s*implemented_by"),
    "classical_choice": re.compile(r"\bClassical\.choice\b"),
    "propext": re.compile(r"\bpropext\b"),
    "quot_sound": re.compile(r"\bQuot\.sound\b"),
    "heartbeats_option": re.compile(r"set_option\s+maxHeartbeats"),
    "synth_instance": re.compile(r"\bsynthInstance\b"),
}
# Names of known upstream placeholders that are statement-only by construction.
STATEMENT_ONLY_HINT = re.compile(r"(statement|Statement|Stmt|Conjecture|conjecture)\s*$")


def package_of(root: Path, path: Path) -> str:
    rel = path.relative_to(root)
    if rel.parts[0] == "formalized-sources":
        return "/".join(rel.parts[:2])
    return rel.parts[0]


def scan_file(path: Path, root: Path):
    text = path.read_text(errors="replace")
    lines = text.splitlines()
    rel = str(path.relative_to(root))
    decls = []
    counts = Counter()
    for i, line in enumerate(lines, 1):
        m = DECL_RE.match(line)
        if m:
            counts[m.group(1)] += 1
            decls.append({"kind": m.group(1), "name": m.group(2), "line": i})
            continue
        m2 = DECL_KIND_ONLY.match(line)
        if m2:
            counts[m2.group(1)] += 1
            decls.append({"kind": m2.group(1), "name": None, "line": i})
    markers = {}
    for name, rx in MARKERS.items():
        hits = [i for i, line in enumerate(lines, 1) if rx.search(line)]
        if hits:
            markers[name] = {"count": len(hits), "lines": hits[:20]}
    namespaces = sorted({NAMESPACE_RE.match(l).group(1) for l in lines if NAMESPACE_RE.match(l)})
    statement_only = [d for d in decls if d["name"] and STATEMENT_ONLY_HINT.search(d["name"])]
    return {
        "file": rel,
        "lines": len(lines),
        "decl_counts": dict(counts),
        "declarations": len(decls),
        "namespaces": namespaces[:20],
        "markers": markers,
        "statement_only_named": len(statement_only),
    }


def main():
    root = Path(sys.argv[1]).resolve()
    out = Path(sys.argv[2]).resolve()
    files = sorted(p for p in root.rglob("*.lean") if ".lake" not in p.parts)
    pkgs = defaultdict(lambda: {
        "files": 0, "lines": 0, "decl_counts": Counter(), "declarations": 0,
        "markers": Counter(), "marker_files": defaultdict(list), "namespaces": set(),
        "statement_only_named": 0, "module_roots": set(),
    })
    file_records = []
    for p in files:
        pkg = package_of(root, p)
        rec = scan_file(p, root)
        file_records.append(rec)
        P = pkgs[pkg]
        P["files"] += 1
        P["lines"] += rec["lines"]
        P["decl_counts"].update(rec["decl_counts"])
        P["declarations"] += rec["declarations"]
        P["statement_only_named"] += rec["statement_only_named"]
        for ns in rec["namespaces"]:
            P["namespaces"].add(ns)
        for name, info in rec["markers"].items():
            P["markers"][name] += info["count"]
            P["marker_files"][name].append(rec["file"])
        # module root: first two path components under package dir
        P["module_roots"].add(rec["file"])

    summary = {}
    for pkg, P in sorted(pkgs.items()):
        summary[pkg] = {
            "files": P["files"],
            "lines": P["lines"],
            "declarations": P["declarations"],
            "decl_counts": dict(P["decl_counts"]),
            "statement_only_named": P["statement_only_named"],
            "markers": dict(P["markers"]),
            "marker_file_counts": {k: len(v) for k, v in P["marker_files"].items()},
            "marker_examples": {k: v[:5] for k, v in P["marker_files"].items()},
            "namespaces": sorted(P["namespaces"])[:40],
        }
    out.write_text(json.dumps({
        "root": str(root),
        "lean_files": len(files),
        "packages": summary,
        "files": file_records,
    }, indent=1))
    print(json.dumps({p: {k: v for k, v in s.items() if k in
                          ("files", "lines", "declarations", "markers", "statement_only_named")}
                      for p, s in summary.items()}, indent=1))


if __name__ == "__main__":
    main()
