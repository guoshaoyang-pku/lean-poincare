#!/usr/bin/env python3
"""D9 third-pass gate 2b: worktree-wide token audit (scope-extension check).

The predecessor audit scanned only release/ (the release package).  The task says
"scan all authored sources (excluding .lake/)".  This runner scans the *whole worktree*
(including tools/, input/, negcontrol/, manifest/) with the same comment/string-aware
lexical classifier, and records every hit with file:line:col.

It separates three scopes:
  * release/ excluding Audit/D9   -> D6-authored release sources
  * release/Audit/D9              -> auditor tooling (self-reference)
  * everything else in the worktree (tools/, input/, negcontrol/)

Output: release/Audit/D9/logs/verify3/token_audit_wide.json
"""
import collections
import json
import os
import tokenize
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
OUTDIR = os.path.join(ROOT, "release", "Audit", "D9", "logs", "verify3")
REQUIRED = ["sorry", "axiom", "unsafe", "native_decide", "proof_wanted", "admit"]
import re
PAT = re.compile(r"\b(" + "|".join(REQUIRED) + r")\b")


def scan_lean(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    hits = []
    i, n = 0, len(text)

    def emit(start, end, cls):
        seg = text[start:end]
        base_line = text.count("\n", 0, start) + 1
        base_col = start - (text.rfind("\n", 0, start) + 1) + 1
        for m in PAT.finditer(seg):
            hits.append((base_line, base_col + m.start(), m.group(1), cls))

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
            j = text.find("\n", i); j = n if j == -1 else j
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
            j = text.find("»", i); j = n if j == -1 else j + 1
            emit(i, j, "escaped_ident"); i = j; continue
        m = PAT.match(text, i)
        if m:
            base_line = text.count("\n", 0, i) + 1
            base_col = i - (text.rfind("\n", 0, i) + 1) + 1
            hits.append((base_line, base_col, m.group(1), "code"))
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
    for t in toks:
        cls = {tokenize.NAME: "code", tokenize.STRING: "string",
               tokenize.COMMENT: "comment"}.get(t.type)
        if cls is None:
            continue
        for m in PAT.finditer(t.string):
            hits.append((t.start[0], t.start[1] + m.start() + 1, m.group(1), cls))
    return hits


def authored(root):
    out = []
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d not in (".lake", ".git", "__pycache__")]
        for f in fn:
            if f.endswith((".lean", ".py")):
                out.append(os.path.relpath(os.path.join(dp, f), root))
    return sorted(out)


def main():
    files = authored(ROOT)
    hits = []
    for rel in files:
        p = os.path.join(ROOT, rel)
        hs = scan_lean(p) if rel.endswith(".lean") else scan_python(p)
        for (line, col, tok, cls) in hs:
            scope = ("d6-release" if rel.startswith("release/") and not rel.startswith("release/Audit/D9/")
                     else "d9-tooling" if rel.startswith("release/Audit/D9/")
                     else "worktree-outside-release")
            hits.append({"file": rel, "line": line, "col": col, "token": tok,
                         "context_class": cls, "scope": scope, "verdict": "FAIL"})
    by_scope = collections.Counter(h["scope"] for h in hits)
    code = [h for h in hits if h["context_class"] == "code"]
    res = {
        "schema": "d9-adversarial-audit/wide-token-audit-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": ROOT, "excluded": [".lake", ".git", "__pycache__"],
        "extensions": [".lean", ".py"],
        "required_tokens": REQUIRED,
        "files_scanned": len(files),
        "required_raw_hits": len(hits),
        "hits_by_scope": dict(by_scope),
        "hits_by_token": dict(collections.Counter(h["token"] for h in hits)),
        "hits_by_class": dict(collections.Counter(h["context_class"] for h in hits)),
        "code_position_hits": code,
        "hits": hits,
    }
    os.makedirs(OUTDIR, exist_ok=True)
    out = os.path.join(OUTDIR, "token_audit_wide.json")
    with open(out, "w") as fh:
        json.dump(res, fh, indent=1)
    print("files:", len(files), "raw hits:", len(hits), "by scope:", dict(by_scope))
    print("code-position hits:", len(code))
    for h in code:
        print("  ", h["file"], h["line"], h["col"], h["token"])
    print("wrote", out)


if __name__ == "__main__":
    main()
