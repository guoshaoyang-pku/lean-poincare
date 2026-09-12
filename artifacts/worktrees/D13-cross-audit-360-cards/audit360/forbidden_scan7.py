#!/usr/bin/env python3
"""Round-7 (invocation 6) forbidden-token scan (same wide token set as round 6).

Comment/string-aware scan of every `.lean` file in each staged card package
(excluding `.lake`), plus the semantic-ledger snapshot package and this audit's
own probe files.  Tokens reported:

  sorry, admit, axiom, unsafe, native_decide, proof_wanted, opaque, extern,
  implemented_by, partial def / partial theorem / partial lemma, `by_contra!`?
  (no), `set_option autoImplicit true`? (no: only soundness escapes).

`axiom` hits that are the documented negative control in the task's own audit
module are reported but tagged.  Fail-closed: a hit in any producer package is a
finding and is listed explicitly.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
PKGS = os.path.join(HERE, "pkgs")
CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics",
    "D12-geometric-compactness", "D12-surgery-recognition",
    "D12-semantic-ledger-snapshot",
]
TOKENS = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"^\s*(private\s+|protected\s+)?axiom\b", re.M)),
    ("unsafe", re.compile(r"^\s*(private\s+|protected\s+)?unsafe\s+(def|theorem|lemma|instance|abbrev|axiom|opaque)\b", re.M)),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("proof_wanted", re.compile(r"\bproof_wanted\b")),
    ("opaque", re.compile(r"^\s*(private\s+|protected\s+)?opaque\b", re.M)),
    ("extern", re.compile(r"@\[\s*extern\b|\bextern\b")),
    ("implemented_by", re.compile(r"implemented_by")),
    ("partial", re.compile(r"^\s*(private\s+|protected\s+)?partial\s+(def|theorem|lemma|instance)\b", re.M)),
    ("set_option_maxHeartbeats_0", re.compile(r"maxHeartbeats\s+0\b")),
    ("byContraBang", re.compile(r"\bby_contra!")),
]


def strip_comments_strings(text):
    """Replace comments and string literals by spaces (nested block comments)."""
    out = []
    i = 0
    n = len(text)
    depth = 0
    in_str = False
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if in_str:
            if c == "\\":
                out.append(" ")
                i += 2
                continue
            if c == '"':
                in_str = False
                out.append(" ")
                i += 1
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                j = n
            out.append(" " * (j - i))
            i = j
            continue
        if c == '"':
            in_str = True
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def main():
    report = {"round": 7, "invocation": 6, "tokens": [t for t, _ in TOKENS],
              "packages": {}, "total_hits": 0}
    for card in CARDS:
        root = os.path.join(PKGS, card)
        hits = []
        nfiles = 0
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d != ".lake"]
            for fn in sorted(filenames):
                if not fn.endswith(".lean"):
                    continue
                nfiles += 1
                path = os.path.join(dirpath, fn)
                raw = open(path, encoding="utf-8", errors="replace").read()
                clean = strip_comments_strings(raw)
                for tok, rx in TOKENS:
                    for m in rx.finditer(clean):
                        line = clean[:m.start()].count("\n") + 1
                        hits.append({"file": os.path.relpath(path, root),
                                     "line": line, "token": tok})
        report["packages"][card] = {"lean_files": nfiles, "hits": hits}
        report["total_hits"] += len(hits)
    report["hits_outside_expected_negcontrol"] = [
        h for card, v in report["packages"].items() for h in v["hits"]
        if not (card == "D12-volume-ibp" and h["file"] == "Poincare/D12/VolumeIBP/AxiomAudit.lean")
    ]
    with open(os.path.join(HERE, "forbidden_scan_round7.json"), "w") as f:
        json.dump(report, f, indent=1)
    print(json.dumps({k: v for k, v in report.items() if k != "packages"}, indent=1))
    for card, v in report["packages"].items():
        if v["hits"]:
            print(card, json.dumps(v["hits"], indent=1))


if __name__ == "__main__":
    main()
