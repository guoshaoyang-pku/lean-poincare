#!/usr/bin/env python3
"""Forbidden-token scan for Lean sources, with comments stripped.

Strips:
  * nested block comments  /- ... -/
  * line comments          -- ... EOL
  * string literals        "..."  (so tokens inside strings are not counted)
Handles Lean's nesting of block comments and simple escapes in strings.
"""
import re, sys

FORBIDDEN = [
    "sorry", "admit", "axiom", "opaque", "unsafe", "extern",
    "implemented_by", "native_decide", "decide!", "#eval", "#exit",
    "run_cmd", "elab ", "macro ", "syntax ", "partial def",
    "by_contra!", "push_neg at", "set_option", "Classical.choice",
    "propext", "Quot.sound", "trustCompiler", "lcProof", "ofReduceBool",
]


def strip_lean(src: str):
    out = []
    i, n = 0, len(src)
    depth = 0  # block-comment depth
    in_str = False
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1; i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; i += 2; continue
            if c == "\n":
                out.append("\n")
            i += 1
            continue
        if in_str:
            if c == "\\" and i + 1 < n:
                i += 2; continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if src.startswith("/-", i):
            depth = 1; i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        if c == '"':
            in_str = True; i += 1; continue
        out.append(c)
        i += 1
    return "".join(out)


def main(path):
    src = open(path, encoding="utf-8").read()
    stripped = strip_lean(src)
    print(f"file: {path}")
    print(f"raw chars: {len(src)}, comment/string-stripped chars: {len(stripped)}")
    hits = 0
    for tok in FORBIDDEN:
        raw_n = src.count(tok)
        st_n = stripped.count(tok)
        if raw_n or st_n:
            hits += 1
            print(f"  token {tok!r}: raw={raw_n} stripped={st_n}")
    if hits == 0:
        print("  no forbidden tokens found in either raw or stripped text")
    # also show stripped file for eyeballing (next to this script, never next to the artifact)
    import os
    outdir = os.path.dirname(os.path.abspath(__file__))
    outpath = os.path.join(outdir, os.path.basename(path) + ".stripped")
    with open(outpath, "w", encoding="utf-8") as f:
        f.write(stripped)
    print(f"stripped copy written to: {outpath}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
