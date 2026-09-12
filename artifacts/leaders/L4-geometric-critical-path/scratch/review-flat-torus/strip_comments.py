#!/usr/bin/env python3
"""Faithful-enough Lean comment stripper used for the M2 delta review.

Removes nested /- ... -/ block comments (incl. /-! docstrings) and -- line
comments, preserving every other byte (including whitespace and line breaks).
String literals are not present in M2; verified by inspection.
"""
import sys
src = open(sys.argv[1]).read()
out = []
i, n, depth = 0, len(src), 0
while i < n:
    if src.startswith('/-', i):
        depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth > 0:
        depth -= 1; i += 2; continue
    if depth > 0:
        i += 1; continue
    if src.startswith('--', i):
        j = src.find('\n', i)
        i = n if j < 0 else j
        continue
    out.append(src[i]); i += 1
open(sys.argv[2], 'w').write(''.join(out))
