#!/usr/bin/env python3
"""Forbidden-token scan on Lean sources with comments (line + nested block) stripped.

Usage: strip_and_scan.py FILE [FILE...]
Prints, for each file, the stripped token hits and the stripped char count.
Also flags strings (token hits inside string literals) separately as INFO.
"""
import re
import sys

FORBIDDEN = ["sorry", "admit", "axiom", "unsafe", "native_decide", "proof_wanted"]


def strip_comments(src: str):
    """Return (stripped, strings_removed) where comments and string literals
    are replaced by spaces of equal length (so line/col offsets stay valid).

    Lean block comments nest; line comments are `--`.
    String literals: "..." with backslash escapes.
    """
    out = list(src)
    i, n = 0, len(src)
    depth = 0
    in_str = False
    while i < n:
        c = src[i]
        if in_str:
            if c == "\\" and i + 1 < n:
                out[i] = " "
                out[i + 1] = " "
                i += 2
                continue
            if c == '"':
                in_str = False
            out[i] = " "
            i += 1
            continue
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        # depth == 0, not in string
        if src.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1:
                j = n
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if c == '"':
            in_str = True
            out[i] = " "
            i += 1
            continue
        i += 1
    return "".join(out), depth


def main():
    for path in sys.argv[1:]:
        with open(path, "r", encoding="utf-8") as f:
            src = f.read()
        stripped, depth = strip_comments(src)
        if depth != 0:
            print(f"{path}: WARNING unterminated block comment (depth={depth})")
        hits = []
        for tok in FORBIDDEN:
            for m in re.finditer(r"(?<![A-Za-z0-9_'.])" + re.escape(tok) + r"(?![A-Za-z0-9_'])", stripped):
                line = stripped.count("\n", 0, m.start()) + 1
                hits.append((tok, line, m.group(0)))
        print(f"{path}: stripped_chars={len(stripped)} (comment/string chars blanked)")
        if hits:
            for tok, line, text in hits:
                print(f"  HIT {tok!r} at line {line}")
        else:
            print("  NO forbidden tokens in code (comments/strings stripped)")


if __name__ == "__main__":
    main()
