#!/usr/bin/env python3
"""Classify the forbidden-token hits of a release mirror, fail closed on any new one.

`check-authored-files.py <root> release` scans the release package with the same
comment/string-aware rules as the adapter contract check, but the release
deliberately contains two kinds of permitted hits:

  * **intentional negative controls** — `axiom` declarations in the D12 audit
    modules whose whole purpose is to be detected by the fail-closed audit (the
    file documents this and the axiom is not imported by any proof module);
  * **audit-tooling pattern matches** — `.«unsafe»` match patterns inside the
    audit programs that inspect declaration safety, not `unsafe` declarations.

Every hit must fall in one of those classes with a machine-checked reason; any
other hit (in particular any `sorry`, `admit`, `native_decide`, `proof_wanted`
or a real `unsafe` declaration) fails the run.

Usage: classify-release-forbidden-hits.py <release-root> [out.json]
"""
import json
import re
import sys
import time
from importlib.machinery import SourceFileLoader
from pathlib import Path

HERE = Path(__file__).resolve().parent
inv = SourceFileLoader("inv2", str(HERE / "inventory-v2.py")).load_module()
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "axiom": re.compile(r"^[ \t]*axiom\b", re.M),
    "admit": re.compile(r"\badmit\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "proof_wanted": re.compile(r"\bproof_wanted\b"),
}
NEG_CONTROL_FILES = {
    "Poincare/D12/TriangulationTopology/NegControl/NegControl.lean",
    "Poincare/D12/VolumeIBP/Audit.lean",
}
NEG_CONTROL_DECL = re.compile(r"axiom\s+(negativeControl|d12NegControlBadAxiom)\b")


def classify(root: Path):
    hits = []
    for p in sorted(root.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        raw = p.read_text(errors="replace")
        code = inv.strip_comments(raw)
        rel = str(p.relative_to(root))
        raw_lines = raw.splitlines()
        for token, rx in FORBIDDEN.items():
            for m in rx.finditer(code):
                line = code[: m.start()].count("\n") + 1
                snippet = raw_lines[line - 1].strip() if line <= len(raw_lines) else ""
                if token == "unsafe" and ".«unsafe»" in snippet:
                    cls = "audit-tooling pattern `.«unsafe»` (declaration-safety scanner), not an unsafe declaration"
                elif token == "axiom" and rel in NEG_CONTROL_FILES and NEG_CONTROL_DECL.search(snippet):
                    cls = "intentional negative-control axiom, documented in-file, not imported by any proof module"
                else:
                    cls = "UNEXPLAINED"
                hits.append({"file": rel, "line": line, "token": token, "snippet": snippet, "class": cls})
    return hits


def main() -> int:
    root = Path(sys.argv[1]).resolve()
    hits = classify(root)
    unexplained = [h for h in hits if h["class"] == "UNEXPLAINED"]
    by_token = {}
    for h in hits:
        by_token[h["token"]] = by_token.get(h["token"], 0) + 1
    report = {
        "schema": "m2/release-forbidden-classification-v1",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "release_root": str(root),
        "hits": hits,
        "by_token": by_token,
        "unexplained": len(unexplained),
    }
    if len(sys.argv) > 2:
        Path(sys.argv[2]).write_text(json.dumps(report, indent=2) + "\n")
    print(f"release forbidden-token scan: {len(hits)} hits {by_token}")
    for h in hits:
        print(f"  {h['file']}:{h['line']} [{h['token']}] -> {h['class'][:70]}")
    if unexplained:
        print(f"UNEXPLAINED FORBIDDEN HITS: {len(unexplained)}")
        print("RELEASE-FORBIDDEN CHECK FAILED")
        return 1
    print("all hits classified; no `sorry`/`admit`/`native_decide`/`proof_wanted`/real-`unsafe` declaration")
    print("RELEASE-FORBIDDEN CHECK PASSED (classified)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
