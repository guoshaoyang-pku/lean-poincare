#!/usr/bin/env python3
"""Strip Lean comments (nested block comments, line comments) and string/char literals,
then scan for forbidden tokens. Read-only w.r.t. artifact."""
import sys, re

def strip_lean(src: str) -> str:
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith('/-', i):
                depth += 1; i += 2; out.append(' ')
            elif src.startswith('-/', i):
                depth -= 1; i += 2; out.append(' ')
            else:
                if c == '\n': out.append('\n')
                else: out.append(' ')
                i += 1
        else:
            if src.startswith('/-', i):
                depth += 1; i += 2; out.append(' ')
            elif src.startswith('--', i):
                j = src.find('\n', i)
                if j == -1: i = n
                else: i = j  # keep newline
                out.append(' ')
            elif c == '"':
                # string literal (handle escapes) - keep a placeholder
                i += 1; out.append('""')
                while i < n:
                    if src[i] == '\\': i += 2; continue
                    if src[i] == '"': i += 1; break
                    i += 1
            elif c == "'":
                # char literal or identifier prime; only treat as char if closing quote soon
                m = re.match(r"'(\\\\.|[^'\\\\])'", src[i:])
                if m:
                    i += m.end(); out.append("''")
                else:
                    out.append(c); i += 1
            else:
                out.append(c); i += 1
    return ''.join(out)

path = sys.argv[1]
src = open(path, encoding='utf-8').read()
stripped = strip_lean(src)
tokens = ['sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'proof_wanted']
found = False
for tok in tokens:
    for m in re.finditer(re.escape(tok), stripped):
        line = stripped[:m.start()].count('\n') + 1
        ctx = stripped.splitlines()[line-1].strip()
        print(f"FOUND {tok!r} at stripped-line {line}: {ctx[:120]}")
        found = True
if not found:
    print("CLEAN: none of", tokens, "occur outside comments/strings")

# Also report raw occurrences with original line numbers for transparency
print("--- raw occurrences (any context) ---")
for tok in tokens:
    hits = [(src[:m.start()].count('\n')+1) for m in re.finditer(re.escape(tok), src)]
    if hits:
        print(f"raw {tok!r}: lines {hits}")
