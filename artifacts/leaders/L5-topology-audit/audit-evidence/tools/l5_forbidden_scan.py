#!/usr/bin/env python3
"""L5 topology audit: comment/string-aware forbidden-token scan of authored Lean files.

Independent re-implementation (not a rerun of any D12/D13 script).  Scans the code text
only: nested block comments, line comments, string and char literals are removed first.
Reports hits for the forbidden constructs and for the documented negative-control axiom
declarations (which are expected, reported, and must not be silently ignored).

Usage: python3 l5_forbidden_scan.py <release-root> <out-json>
"""
import json
import pathlib
import re
import sys

FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "axiom": re.compile(r"(?<![\w.])axiom\b"),
    "admit": re.compile(r"\badmit\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "proof_wanted": re.compile(r"\bproof_wanted\b"),
    "sorryAx": re.compile(r"\bsorryAx\b"),
}


def strip_comments_strings(src: str) -> str:
    """Return src with comments and string/char literal contents replaced by spaces."""
    out = []
    i, n = 0, len(src)
    depth = 0  # block comment nesting
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
            continue
        if c == '"':
            out.append(" ")
            i += 1
            while i < n:
                if src[i] == "\\":
                    out.append("  ")
                    i += 2
                    continue
                if src[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
            continue
        if c == "'":
            # char literal ('a', '\n', '\'') or syntax quotation; only treat as literal
            # when a closing quote occurs within 6 chars without newline.
            m = re.match(r"'(\\.[^']*|[^'\\\n])'", src[i:])
            if m:
                out.append(" " * len(m.group(0)))
                i += len(m.group(0))
                continue
        out.append(c)
        i += 1
    return "".join(out)


def main() -> int:
    root = pathlib.Path(sys.argv[1]).resolve()
    out_json = pathlib.Path(sys.argv[2]).resolve()
    files = sorted(p for p in root.rglob("*.lean") if ".lake" not in p.parts)
    hits = {k: [] for k in FORBIDDEN}
    scanned = 0
    for p in files:
        raw = p.read_text(encoding="utf-8", errors="replace")
        code = strip_comments_strings(raw)
        scanned += 1
        rel = "./" + str(p.relative_to(root))
        for lineno, line in enumerate(code.splitlines(), 1):
            for key, rx in FORBIDDEN.items():
                if rx.search(line):
                    hits[key].append({"file": rel, "line": lineno, "text": line.strip()[:160]})
    result = {
        "scanner": "l5_forbidden_scan.py (comment/string aware, independent implementation)",
        "root": str(root),
        "lean_files_scanned": scanned,
        "forbidden_hits": hits,
        "total_hits": sum(len(v) for v in hits.values()),
    }
    out_json.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps({k: len(v) for k, v in hits.items()}, indent=1))
    print("files scanned:", scanned)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
