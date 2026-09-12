#!/usr/bin/env python3
"""SEMREV-L3 independent scan: file set, hashes, forbidden tokens.

Independent re-implementation (not a re-run of tools/l3_check.py).

  * enumerates every .lean file under Poincare/L3 (must be exactly the six authored files)
  * sha256 of each, compared against the parent's authored-hashes.txt
  * comment/string-aware forbidden-token scan for
    sorry / axiom / admit / unsafe / native_decide / proof_wanted
  * raw-text scan (including comments) reported separately, so nothing hides in a docstring
  * informational scan for partial / opaque / set_option / #eval

Writes JSON to evidence/semrev-forbidden-scan.json and prints a summary.
Exit code 0 iff no violation and hashes match.
"""

import hashlib
import json
import re
import sys
from pathlib import Path

REVIEW = Path(__file__).resolve().parent.parent
RELEASE = REVIEW / "release"
EVIDENCE = REVIEW / "evidence"
PARENT_HASHES = REVIEW / "parent-authored-hashes.txt"

FORBIDDEN = ["sorry", "axiom", "admit", "unsafe", "native_decide", "proof_wanted"]
INFORMATIONAL = ["partial", "opaque", "set_option", "#eval", "implemented_by", "extern"]


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def strip_comments_strings(text: str) -> str:
    """Independent comment/string stripper (nested block comments, line comments, strings)."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            out.append('"')
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append("  ")
                    i += 2
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
            if i < n:
                out.append('"')
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def token_hits(code: str, tokens):
    hits = []
    for tok in tokens:
        for m in re.finditer(r"(?<![A-Za-z0-9_'.])" + re.escape(tok) + r"(?![A-Za-z0-9_'])", code):
            hits.append({"token": tok, "line": code[: m.start()].count("\n") + 1})
    return hits


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    files = sorted(RELEASE.glob("Poincare/L3/**/*.lean"))
    parent = {}
    if PARENT_HASHES.exists():
        for line in PARENT_HASHES.read_text().splitlines():
            if line.strip():
                h, p = line.split(None, 1)
                p = p.strip()
                if p.startswith("release/"):
                    p = p[len("release/"):]
                parent[p] = h
    pins = {p: h for p, h in parent.items() if not p.startswith("Poincare/")}
    parent = {p: h for p, h in parent.items() if p.startswith("Poincare/")}
    records, violations = [], []
    for p in files:
        rel = str(p.relative_to(RELEASE))
        raw = p.read_text(encoding="utf-8")
        code = strip_comments_strings(raw)
        rec = {
            "path": rel,
            "sha256": sha256(p),
            "lines": raw.count("\n") + 1,
            "forbidden_in_code": token_hits(code, FORBIDDEN),
            "forbidden_in_raw_text": token_hits(raw, FORBIDDEN),
            "informational": token_hits(code, INFORMATIONAL),
        }
        rec["hash_matches_parent_claim"] = parent.get(rel) == rec["sha256"]
        records.append(rec)
        if rec["forbidden_in_code"]:
            violations.append(rec)
    parent_only = sorted(set(parent) - {r["path"] for r in records})
    missing_from_parent = sorted({r["path"] for r in records} - set(parent))
    hash_mismatch = [r["path"] for r in records if not r["hash_matches_parent_claim"]]
    pin_records = {}
    for p, h in pins.items():
        f = RELEASE / p
        pin_records[p] = {
            "claimed": h,
            "actual": sha256(f) if f.exists() else None,
            "matches": f.exists() and sha256(f) == h,
        }
    report = {
        "file_count": len(records),
        "files": records,
        "violations_in_code": violations,
        "raw_text_hits": [r for r in records if r["forbidden_in_raw_text"]],
        "files_in_parent_claim_but_absent_here": parent_only,
        "files_here_not_in_parent_claim": missing_from_parent,
        "hash_mismatches": hash_mismatch,
        "pins": pin_records,
        "ok": not violations and not hash_mismatch and not parent_only and not missing_from_parent
        and len(records) == 6 and all(v["matches"] for v in pin_records.values()),
    }
    out = EVIDENCE / "semrev-forbidden-scan.json"
    out.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: report[k] for k in
                      ("file_count", "violations_in_code", "raw_text_hits", "hash_mismatches",
                       "files_in_parent_claim_but_absent_here", "files_here_not_in_parent_claim",
                       "ok")}, indent=1))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
