#!/usr/bin/env python3
"""D9 post-hoc verification gate 2: strict token audit (own implementation).

Scans every authored source under release/ (excluding .lake/ and .git/) with the
extension set {.lean, .py}.  Required tokens: sorry, axiom, unsafe, native_decide,
proof_wanted, admit.  Every raw occurrence is recorded with "verdict": "FAIL" (the
task's literal rule) plus an exact lexical classification (code / line_comment /
block_comment / string / escaped_ident), produced by a comment- and string-aware
scanner written for this verification pass (nested block comments handled).

Output: release/Audit/D9/logs/verify/token_audit.json
"""
import json
import os
import re
import sys
import tokenize
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
RELEASE = os.path.join(ROOT, "release")
OUTDIR = os.path.join(RELEASE, "Audit", "D9", "logs", "verify")
REQUIRED = ["sorry", "axiom", "unsafe", "native_decide", "proof_wanted", "admit"]
EXTRA = ["sorryAx", "implemented_by", "extern", "opaque", "partial", "set_option"]
ALL = REQUIRED + EXTRA
PAT = re.compile(r"\b(" + "|".join(re.escape(t) for t in ALL) + r")\b")


def scan_lean(path):
    """Return [(line, col, token, cls, text)]. Single pass, nested block comments."""
    text = open(path, encoding="utf-8", errors="replace").read()
    hits = []
    i, n, line, col = 0, len(text), 1, 1
    state = []  # per-line output buffer
    line_start = 0

    def emit(start, end, cls):
        seg = text[start:end]
        base_line = text.count("\n", 0, start) + 1
        base_col = start - (text.rfind("\n", 0, start) + 1) + 1
        for m in PAT.finditer(seg):
            hits.append((base_line, base_col + m.start(), m.group(1), cls,
                         text.splitlines()[base_line - 1].strip()[:200]))

    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            emit(i, j, "block_comment"); i = j; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            emit(i, j, "line_comment"); i = j; continue
        if text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2; continue
                if text[j] == '"':
                    j += 1; break
                j += 1
            emit(i, j, "string"); i = j; continue
        if text[i] == "«":
            j = text.find("»", i)
            j = n if j == -1 else j + 1
            emit(i, j, "escaped_ident"); i = j; continue
        m = PAT.match(text, i)
        if m:
            base_line = text.count("\n", 0, i) + 1
            base_col = i - (text.rfind("\n", 0, i) + 1) + 1
            hits.append((base_line, base_col, m.group(1), "code",
                         text.splitlines()[base_line - 1].strip()[:200]))
            i += len(m.group(1)); continue
        i += 1
    return hits


def scan_python(path):
    hits = []
    data = open(path, "rb").read()
    try:
        toks = list(tokenize.tokenize(iter(data.splitlines(True)).__next__))
    except Exception:
        return hits
    lines = data.decode("utf-8", "replace").splitlines()
    for t in toks:
        cls = {tokenize.NAME: "code", tokenize.STRING: "string",
               tokenize.COMMENT: "comment"}.get(t.type)
        if cls is None:
            continue
        for m in PAT.finditer(t.string):
            ln = t.start[0]
            hits.append((ln, t.start[1] + m.start() + 1, m.group(1), cls,
                         lines[ln - 1].strip()[:200] if ln - 1 < len(lines) else ""))
    return hits


def authored(root):
    out = []
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d not in (".lake", ".git")]
        for f in fn:
            if f.endswith((".lean", ".py")):
                out.append(os.path.relpath(os.path.join(dp, f), root))
    return sorted(out)


def main():
    files = authored(RELEASE)
    all_hits = []
    for rel in files:
        p = os.path.join(RELEASE, rel)
        hits = scan_lean(p) if rel.endswith(".lean") else scan_python(p)
        for (line, col, tok, cls, text) in hits:
            all_hits.append({"file": rel, "line": line, "col": col, "token": tok,
                             "context_class": cls, "text": text,
                             "verdict": "FAIL"})
    req = [h for h in all_hits if h["token"] in REQUIRED]
    d6 = [h for h in req if not h["file"].startswith("Audit/D9/")]
    d9 = [h for h in req if h["file"].startswith("Audit/D9/")]
    by_tok = {t: sum(1 for h in req if h["token"] == t) for t in REQUIRED}
    by_cls = {}
    for h in req:
        by_cls[h["context_class"]] = by_cls.get(h["context_class"], 0) + 1
    res = {
        "schema": "d9-adversarial-audit/verify-token-audit-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "scanner": "D9VerifyTokens.py (post-hoc verification, own implementation)",
        "root": "release/", "excluded": [".lake", ".git"],
        "extensions": [".lean", ".py"],
        "required_tokens": REQUIRED, "supplementary_tokens": EXTRA,
        "files_scanned": len(files),
        "required_raw_hits": len(req),
        "required_raw_hits_d6_authored": len(d6),
        "required_raw_hits_d9_tooling": len(d9),
        "required_by_token": by_tok,
        "required_by_class": by_cls,
        "required_code_position_hits": [h for h in req if h["context_class"] == "code"],
        "d6_code_position_hits": [h for h in d6 if h["context_class"] == "code"],
        "all_tokens_including_supplementary": len(all_hits),
        "hits": all_hits,
    }
    os.makedirs(OUTDIR, exist_ok=True)
    with open(os.path.join(OUTDIR, "token_audit.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    print("files:", len(files), "required hits:", len(req), by_tok)
    print("by class:", by_cls)
    print("D6-authored required hits:", len(d6), "code-position:", len(res["d6_code_position_hits"]))
    print("code-position hits (all):", len(res["required_code_position_hits"]))
    for h in res["required_code_position_hits"]:
        print("  ", h["file"], h["line"], h["col"], h["token"])
    print("wrote", os.path.join(OUTDIR, "token_audit.json"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
