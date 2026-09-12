#!/usr/bin/env python3
"""Adversarial-review tool: forbidden-token scan over M3 with comments stripped.

Handles Lean's nested block comments (/-- ... -/, /- ... -/) and line comments (--),
while respecting string literals so that a '--' inside a string is not treated as a
comment.  Reports both the naive scan (raw text) and the stripped scan.
"""
import re
import sys
import json

TOKENS = ["sorry", "admit", "axiom", "unsafe", "native_decide", "proof_wanted"]
EXTRA = ["sorryAx", "set_option", "implemented_by", "partial", "opaque", "extern",
         "#exit", "by exact?", "native_decide", "run_tac", "simp?"]


def strip_comments(src: str):
    """Return (stripped_code, list_of_(line,col,text) comment spans)."""
    out = []
    i = 0
    n = len(src)
    line = 1
    while i < n:
        c = src[i]
        if c == '"':
            # string literal
            out.append(c)
            i += 1
            while i < n:
                if src[i] == '\\':
                    out.append(src[i:i+2])
                    i += 2
                    continue
                out.append(src[i])
                if src[i] == '"':
                    i += 1
                    break
                if src[i] == '\n':
                    line += 1
                i += 1
            continue
        if c == '-' and i + 1 < n and src[i+1] == '-':
            while i < n and src[i] != '\n':
                i += 1
            continue
        if c == '/' and i + 1 < n and src[i+1] == '-':
            depth = 0
            while i < n:
                if src[i] == '/' and i + 1 < n and src[i+1] == '-':
                    depth += 1
                    i += 2
                    continue
                if src[i] == '-' and i + 1 < n and src[i+1] == '/':
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                    continue
                if src[i] == '\n':
                    line += 1
                i += 1
            continue
        if c == '\n':
            line += 1
        out.append(c)
        i += 1
    return ''.join(out)


def scan(text, tokens):
    hits = []
    for tok in tokens:
        for m in re.finditer(r'(?<![A-Za-z0-9_.])' + re.escape(tok) + r'(?![A-Za-z0-9_])', text):
            ln = text.count('\n', 0, m.start()) + 1
            hits.append((tok, ln, text.splitlines()[ln-1].strip()[:120]))
    return hits


def main(path):
    src = open(path, encoding='utf-8').read()
    stripped = strip_comments(src)
    # sanity: line counts must agree
    print(f"file: {path}")
    print(f"raw lines: {src.count(chr(10))+1}, stripped lines: {stripped.count(chr(10))+1}")
    naive = scan(src, TOKENS + EXTRA)
    strip_hits = scan(stripped, TOKENS + EXTRA)
    print(f"\n--- NAIVE scan (raw text incl. comments) for {TOKENS + EXTRA} ---")
    if not naive:
        print("(no hits)")
    for tok, ln, txt in naive:
        print(f"  {tok!r} at line {ln}: {txt}")
    print(f"\n--- STRIPPED scan (comments removed) for {TOKENS + EXTRA} ---")
    if not strip_hits:
        print("(no hits)")
    for tok, ln, txt in strip_hits:
        print(f"  {tok!r} at line {ln}: {txt}")
    print("\n--- stripped code (for manual inspection) ---")
    print(stripped)


if __name__ == '__main__':
    main(sys.argv[1])
