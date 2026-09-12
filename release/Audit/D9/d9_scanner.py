#!/usr/bin/env python3
"""D9 independent forbidden-token scanner.

Differences from the consumed D5/D6 scanner (`d6_reference_scanner.py`):
  * quoted identifiers `<<...>>` (Lean: guillemets) are handled *before* comment
    detection, so `--` / `/-` inside them cannot desynchronise the lexer;
  * character literals are ignored (single quote) but the scanner also reports
    `sorryAx`, `implemented_by`, `extern`, `opaque`, `set_option ... sorry`? no;
  * both a raw byte-level scan and a code-position scan are produced, so a hit
    hidden in a comment/string is still recorded as evidence;
  * scans every authored text file (not just *.lean) for the raw pass.

Usage: d9_scanner.py <root> [<root> ...]
Prints JSON to stdout. Exit 1 iff a hard token occurs in code position.
"""
import json
import os
import re
import sys

HARD = ["sorry", "axiom", "unsafe", "native_decide", "proof_wanted", "admit", "sorryAx"]
SOFT = ["implemented_by", "extern", "opaque", "partial"]
# word-boundary regexes over code-position text
PATTERNS = {t: re.compile(r"(?<![A-Za-z0-9_'\u00ab\u00bb])" + re.escape(t)
                          + r"(?![A-Za-z0-9_'\u00ab\u00bb])") for t in HARD + SOFT}
TEXT_EXT = {".lean", ".py", ".toml", ".json", ".md", ".txt", ".sh", ".yml", ".yaml"}


def code_mask(text):
    """Blank out comments, strings and quoted identifiers, preserving newlines
    and column positions.  Returns code text of the same length."""
    out = []
    i, n = 0, len(text)
    state = "code"
    depth = 0
    while i < n:
        c = text[i]
        if state == "code":
            # quoted identifier: must be handled before comments
            if c == "\u00ab":  # <<
                j = text.find("\u00bb", i + 1)
                if j == -1:
                    j = n - 1
                out.append(" " * (j - i + 1))
                i = j + 1
                continue
            if c == "-" and i + 1 < n and text[i + 1] == "-":
                state = "line"; out.append("  "); i += 2; continue
            if c == "/" and i + 1 < n and text[i + 1] == "-":
                state = "block"; depth = 1; out.append("  "); i += 2; continue
            if c == '"':
                state = "string"; out.append(" "); i += 1; continue
            out.append(c); i += 1
        elif state == "line":
            if c == "\n":
                state = "code"; out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif state == "block":
            if c == "/" and i + 1 < n and text[i + 1] == "-":
                depth += 1; out.append("  "); i += 2
            elif c == "-" and i + 1 < n and text[i + 1] == "/":
                depth -= 1; out.append("  "); i += 2
                if depth == 0:
                    state = "code"
            else:
                out.append("\n" if c == "\n" else " "); i += 1
        elif state == "string":
            if c == "\\":
                out.append("  "); i += 2
            elif c == '"':
                state = "code"; out.append(" "); i += 1
            else:
                out.append("\n" if c == "\n" else " "); i += 1
    return "".join(out)


def scan_lean(path, rel):
    text = open(path, encoding="utf-8", errors="replace").read()
    code = code_mask(text)
    raw_lines = text.splitlines()
    code_lines = code.splitlines()
    matches = []
    for lineno, line in enumerate(code_lines, 1):
        for tok, pat in PATTERNS.items():
            for m in pat.finditer(line):
                matches.append({
                    "token": tok, "line": lineno, "col": m.start() + 1,
                    "hard": tok in HARD,
                    "code_context": (raw_lines[lineno - 1].strip()[:200]
                                     if lineno - 1 < len(raw_lines) else ""),
                })
    return matches


def raw_scan(path, rel):
    """byte-level token hits regardless of position (comments/strings too)."""
    hits = []
    try:
        lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
    except OSError:
        return hits
    for lineno, line in enumerate(lines, 1):
        for tok in HARD + SOFT:
            for m in re.finditer(r"\b" + re.escape(tok) + r"\b", line):
                hits.append({"token": tok, "line": lineno, "col": m.start() + 1,
                             "context": line.strip()[:200]})
    return hits


def main(argv):
    roots, excludes = [], []
    it = iter(argv[1:])
    for a in it:
        if a == "--exclude":
            excludes.append(next(it))
        else:
            roots.append(a)
    if not roots:
        print("usage: d9_scanner.py [--exclude <rel-prefix>] <root> [<root> ...]", file=sys.stderr)
        return 2
    code_hits, raw_hits, files = [], [], 0
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in (".lake", ".git")]
            dirnames[:] = [d for d in dirnames
                           if os.path.relpath(os.path.join(dirpath, d), root) not in excludes]
            for fn in sorted(filenames):
                path = os.path.join(dirpath, fn)
                ext = os.path.splitext(fn)[1]
                if ext not in TEXT_EXT:
                    continue
                rel = os.path.join(os.path.relpath(root, os.path.dirname(root)), os.path.relpath(path, root))
                rel = os.path.relpath(path, root)
                if ext == ".lean":
                    files += 1
                    for m in scan_lean(path, rel):
                        m["file"] = rel
                        code_hits.append(m)
                for m in raw_scan(path, rel):
                    m["file"] = rel
                    raw_hits.append(m)
    hard = [m for m in code_hits if m["hard"]]
    soft = [m for m in code_hits if not m["hard"]]
    result = {
        "schema": "d9-adversarial-audit/forbidden-scan-v1",
        "roots": roots,
        "lean_files_scanned": files,
        "hard_tokens": HARD,
        "soft_tokens": SOFT,
        "code_hard_match_count": len(hard),
        "code_soft_match_count": len(soft),
        "raw_match_count": len(raw_hits),
        "code_matches": code_hits,
        "raw_matches": raw_hits,
    }
    print(json.dumps(result, indent=1))
    return 1 if hard else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
