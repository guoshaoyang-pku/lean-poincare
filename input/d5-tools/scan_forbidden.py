#!/usr/bin/env python3
"""
D5-clean-rebuild: comment/string-aware forbidden-token scan of the collected
release sources.

Hard-forbidden in code: sorry, axiom (declaration keyword), unsafe, native_decide,
proof_wanted, sorryAx, admit.
Also reported (not part of the hard gate): implemented_by, extern.

Usage: scan_forbidden.py <root> [more roots...]
Writes JSON to stdout; exit code 1 iff a hard-forbidden token occurs in code.
"""
import json
import os
import re
import sys

HARD = ["sorry", "axiom", "unsafe", "native_decide", "proof_wanted", "sorryAx", "admit"]
SOFT = ["implemented_by", "extern"]
PATTERNS = {t: re.compile(r"\b" + re.escape(t) + r"\b") for t in HARD + SOFT}


def strip_comments_and_strings(text):
    """Return (code_text_with_same_newlines, removed_spans). Comments/strings are
    blanked out (spaces kept) so line numbers stay exact."""
    out = []
    i, n = 0, len(text)
    state = "code"          # code | line | block | string
    depth = 0
    while i < n:
        c = text[i]
        if state == "code":
            if c == "-" and i + 1 < n and text[i + 1] == "-":
                state = "line"
                out.append("  ")
                i += 2
                continue
            if c == "/" and i + 1 < n and text[i + 1] == "-":
                state = "block"
                depth = 1
                out.append("  ")
                i += 2
                continue
            if c == '"':
                state = "string"
                out.append(" ")
                i += 1
                continue
            out.append(c)
            i += 1
        elif state == "line":
            if c == "\n":
                state = "code"
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif state == "block":
            if c == "/" and i + 1 < n and text[i + 1] == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif c == "-" and i + 1 < n and text[i + 1] == "/":
                depth -= 1
                out.append("  ")
                i += 2
                if depth == 0:
                    state = "code"
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif state == "string":
            if c == "\\":
                out.append("  ")
                i += 2
            elif c == '"':
                state = "code"
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
    return "".join(out)


def scan_file(path):
    text = open(path, encoding="utf-8").read()
    code = strip_comments_and_strings(text)
    # Escaped identifiers `.«unsafe»` are identifiers, not the keyword.
    code = re.sub(r"«[^»\n]*»", lambda m: " " * len(m.group(0)), code)
    lines = code.splitlines()
    matches = []
    for lineno, line in enumerate(lines, 1):
        for tok, pat in PATTERNS.items():
            for m in pat.finditer(line):
                matches.append({
                    "token": tok,
                    "line": lineno,
                    "col": m.start() + 1,
                    "hard": tok in HARD,
                    "context": text.splitlines()[lineno - 1].strip()[:160],
                })
    return matches


def main(argv):
    roots = argv[1:]
    if not roots:
        print("usage: scan_forbidden.py <root> [more roots...]", file=sys.stderr)
        return 2
    all_matches = []
    files = 0
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in (".lake", ".git")]
            for fn in sorted(filenames):
                if not fn.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, fn)
                files += 1
                for m in scan_file(path):
                    m["file"] = os.path.relpath(path, root)
                    all_matches.append(m)
    hard = [m for m in all_matches if m["hard"]]
    soft = [m for m in all_matches if not m["hard"]]
    result = {
        "schema": "d5-clean-rebuild/forbidden-scan-v1",
        "roots": roots,
        "lean_files_scanned": files,
        "hard_forbidden": HARD,
        "soft_flags": SOFT,
        "hard_match_count": len(hard),
        "soft_match_count": len(soft),
        "matches": all_matches,
    }
    print(json.dumps(result, indent=1))
    return 1 if hard else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
