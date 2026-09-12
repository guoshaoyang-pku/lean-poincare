#!/usr/bin/env python3
"""D9 independent gate 2 (v2): strict token audit of all authored sources under release/ (excl .lake).

Required tokens: sorry, axiom, unsafe, native_decide, proof_wanted, admit.
Supplementary: sorryAx, implemented_by, extern, opaque, partial, set_option.

Every raw hit is recorded with "verdict": "FAIL" (task rule) plus an exact lexical
classification.  Lean: comment/string aware scanner that also treats `.«unsafe»` as an
escaped identifier (not the keyword).  Python: stdlib tokenize (comments/strings exact).

Output: release/Audit/D9/logs/d9b/token_audit.json
"""
import io
import json
import os
import re
import sys
import tokenize
from datetime import datetime, timezone

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
RELEASE = os.path.join(ROOT, "release")
OUTDIR = os.path.join(RELEASE, "Audit", "D9", "logs", "d9b")
REQUIRED = ["sorry", "axiom", "unsafe", "native_decide", "proof_wanted", "admit"]
EXTRA = ["sorryAx", "implemented_by", "extern", "opaque", "partial", "set_option"]
ALL = REQUIRED + EXTRA
PAT = re.compile(r"\b(" + "|".join(re.escape(t) for t in ALL) + r")\b")
# `.«unsafe»` (and any guillemet-quoted identifier) is not a keyword use
GUILLEMET = re.compile(r"\.«([^»]*)»")
# `#print axioms`, `axioms` ok by \b; but `axiom` inside `s!"..."` is a string


def authored_sources(root):
    out = []
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d not in (".lake", ".git")]
        for f in fn:
            if f.endswith(".lean") or f.endswith(".py"):
                out.append(os.path.relpath(os.path.join(dp, f), root))
    return sorted(out)


def classify_lean_line(line, in_block):
    """Yield (col0, token, cls) and return new in_block state. cls in
    code/line_comment/block_comment/string/escaped_ident."""
    out = []
    n = len(line)
    j = 0
    in_str = False
    while j < n:
        if in_block:
            k = line.find("-/", j)
            seg_end = n if k == -1 else k
            for m in PAT.finditer(line, j, seg_end):
                out.append((m.start(), m.group(1), "block_comment"))
            if k == -1:
                return out, True
            in_block = False
            j = k + 2
            continue
        if in_str:
            k = line.find('"', j)
            seg_end = n if k == -1 else k
            for m in PAT.finditer(line, j, seg_end):
                out.append((m.start(), m.group(1), "string"))
            if k == -1:
                return out, False
            in_str = False
            j = k + 1
            continue
        lc = line.find("--", j)
        bc = line.find("/-", j)
        st = line.find('"', j)
        nxt = min([x for x in (lc, bc, st, n) if x != -1])
        for m in PAT.finditer(line, j, nxt):
            # escaped identifier?
            pre = line[max(0, m.start() - 1):m.start()]
            if pre == "«":
                cls = "escaped_ident"
            else:
                cls = "code"
            out.append((m.start(), m.group(1), cls))
        if nxt == n:
            break
        if nxt == lc:
            for m in PAT.finditer(line, lc, n):
                out.append((m.start(), m.group(1), "line_comment"))
            break
        if nxt == bc:
            in_block = True
            j = bc + 2
            continue
        in_str = True
        j = st + 1
    return out, in_block


def scan_lean(path):
    hits = []
    with open(path, encoding="utf-8", errors="replace") as fh:
        lines = fh.readlines()
    in_block = False
    for i, line in enumerate(lines, start=1):
        found, in_block = classify_lean_line(line.rstrip("\n"), in_block)
        for (col0, tok, cls) in found:
            hits.append((i, col0 + 1, tok, cls, line.rstrip("\n")))
    return hits


def scan_python(path):
    hits = []
    with open(path, "rb") as fh:
        try:
            toks = list(tokenize.tokenize(fh.readline))
        except tokenize.TokenError:
            return hits
    lines = open(path, encoding="utf-8", errors="replace").readlines()
    for t in toks:
        if t.type not in (tokenize.NAME, tokenize.STRING, tokenize.COMMENT):
            continue
        if t.type == tokenize.NAME and t.string not in ALL:
            continue
        text = t.string
        cls = {tokenize.NAME: "code", tokenize.STRING: "string",
               tokenize.COMMENT: "comment"}[t.type]
        for m in PAT.finditer(text):
            hits.append((t.start[0], t.start[1] + m.start() + 1, m.group(1), cls,
                         lines[t.start[0] - 1].rstrip("\n") if t.start[0] - 1 < len(lines) else ""))
    return hits


def main():
    os.makedirs(OUTDIR, exist_ok=True)
    files = authored_sources(RELEASE)
    all_hits = []
    per_file = {}
    for rel in files:
        p = os.path.join(RELEASE, rel)
        hits = scan_lean(p) if rel.endswith(".lean") else scan_python(p)
        per_file[rel] = {"total": len(hits),
                         "code": sum(1 for h in hits if h[3] == "code")}
        for (line, col, tok, cls, text) in hits:
            all_hits.append({
                "file": rel, "line": line, "col": col, "token": tok,
                "context_class": cls, "text": text.strip()[:200],
                "verdict": "FAIL",  # task rule: every raw hit is a FAIL
            })
    code_hits = [h for h in all_hits if h["context_class"] == "code"]
    d9 = [h for h in all_hits if h["file"].startswith("Audit/D9/")]
    # release = D6-authored (everything the D6 package contains; D9 tooling is auditor-added)
    release_hits = [h for h in all_hits if not h["file"].startswith("Audit/D9/")]
    release_code = [h for h in release_hits if h["context_class"] == "code"]
    result = {
        "schema": "d9-adversarial-audit/indep-token-audit-v2",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": "release/", "excluded": [".lake", ".git"],
        "extensions": [".lean", ".py"],
        "required_tokens": REQUIRED, "supplementary_tokens": EXTRA,
        "files_scanned": len(files),
        "raw_hit_count": len(all_hits),
        "raw_hits_by_token": {t: sum(1 for h in all_hits if h["token"] == t) for t in ALL},
        "raw_hits_by_class": {c: sum(1 for h in all_hits if h["context_class"] == c)
                              for c in ["code", "line_comment", "block_comment", "string",
                                        "escaped_ident", "comment"]},
        "code_position_hits": code_hits,
        "release_raw_hit_count": len(release_hits),
        "release_code_position_hits": release_code,
        "d9_tooling_hits": len(d9),
        "hits": all_hits,
        "per_file_counts": per_file,
    }
    out = os.path.join(OUTDIR, "token_audit.json")
    with open(out, "w") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps({k: result[k] for k in
                      ["files_scanned", "raw_hit_count", "raw_hits_by_token",
                       "raw_hits_by_class", "release_raw_hit_count"]}, indent=1))
    print("code-position hits (all):", len(code_hits))
    print("code-position hits (D6 release, excl Audit/D9):", len(release_code))
    for h in release_code:
        print(f"  {h['file']}:{h['line']}:{h['col']} {h['token']} :: {h['text']}")
    print("wrote", out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
