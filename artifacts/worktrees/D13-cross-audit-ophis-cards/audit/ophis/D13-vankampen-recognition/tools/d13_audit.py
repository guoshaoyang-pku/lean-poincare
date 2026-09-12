#!/usr/bin/env python3
"""D13-vankampen-recognition: fail-closed programmatic axiom audit + forbidden scan.

1. Extracts every top-level declaration name from the four authored D13 modules.
2. Generates `release/Poincare/D13/VanKampenRecognition/Audit.lean` with one
   `#print axioms` per declaration.
3. Builds the audit module and parses every block; FAILS unless every axiom
   cone is a subset of {propext, Classical.choice, Quot.sound} (so `sorryAx`,
   `unsafe`-attached axioms etc. fail).
4. Runs a nested-comment/string-aware forbidden scan over the authored sources:
   `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted` must not
   appear outside comments and strings.

Usage:
    python3 tools/d13_audit.py
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

MODULES = [
    "Poincare/D13/VanKampenRecognition/FreeProduct.lean",
    "Poincare/D13/VanKampenRecognition/Stereographic.lean",
    "Poincare/D13/VanKampenRecognition/SphereVanKampen.lean",
    "Poincare/D13/VanKampenRecognition/SR4Closure.lean",
]

DECL_RE = re.compile(r"^(?:(?:@\[\S+\]|@\[\w+ .*?\])\s+)*(theorem|lemma|def|instance|structure|abbrev|class)\s+([\w'.\u2080-\u2099]+)")
NS_RE = re.compile(r"^namespace\s+([\w.]+)")
END_RE = re.compile(r"^end\s+([\w.]+)?")

BLOCK_RE = re.compile(r"'([^']+)' (depends on axioms: (\[[^\]]*\])|does not depend on any axioms)")


def extract_decls(path: Path):
    names = []
    ns = []
    for line in path.read_text().splitlines():
        m = END_RE.match(line)
        if m and ns:
            ns.pop()
            continue
        m = NS_RE.match(line)
        if m:
            ns.append(m.group(1))
            continue
        m = DECL_RE.match(line)
        if m:
            names.append(".".join(ns + [m.group(2)]))
    return names


def strip_comments_and_strings(text: str) -> str:
    out = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c == '/' and i + 1 < n and text[i + 1] == '-':
            # block or doc comment (nested aware)
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if text.startswith('/-', j):
                    depth += 1
                    j += 2
                elif text.startswith('-/', j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            i = j
            out.append(' ')
            continue
        if c == '-' and i + 1 < n and text[i + 1] == '-':
            j = text.find('\n', i)
            i = n if j == -1 else j
            out.append(' ')
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                if text[j] == '\\':
                    j += 1
                j += 1
            i = j + 1
            out.append(' ')
            continue
        out.append(c)
        i += 1
    return ''.join(out)


FORBIDDEN = ["sorry", "axiom", "admit", "unsafe", "native_decide", "proof_wanted"]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    release = root / "release"
    audit_path = release / "Poincare/D13/VanKampenRecognition/Audit.lean"

    decls = []
    for mod in MODULES:
        decls.extend(extract_decls(release / mod))
    decls = list(dict.fromkeys(decls))
    print(f"extracted {len(decls)} declarations from {len(MODULES)} modules")

    header = '''/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-vankampen-recognition)

**D13 van Kampen recognition: fail-closed axiom audit.**

Every declaration of the four authored D13 modules is passed through
`#print axioms`.  The accepted cone is `{}`, `{propext}`, `{Classical.choice}`,
`{Quot.sound}` and combinations.  Any other axiom — `sorryAx` in particular —
fails the audit.  Generated from the declaration list of the audited modules.
-/
import Poincare.D13.VanKampenRecognition.All

namespace Poincare.D13.VanKampenRecognition

'''
    lines = [header]
    for d in decls:
        lines.append(f"#print axioms {d}")
    lines.append("")
    lines.append("end Poincare.D13.VanKampenRecognition")
    lines.append("")
    audit_path.write_text("\n".join(lines))

    proc = subprocess.run(
        ["lake", "env", "lean", "Poincare/D13/VanKampenRecognition/Audit.lean"],
        cwd=release, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print("FAIL: audit module did not compile")
        print(out[-4000:])
        return 1

    blocks = BLOCK_RE.findall(out)
    seen = {name: (g3 if g3 else "") for name, _, g3 in blocks}
    if len(seen) < len(decls):
        missing = [d for d in decls if d not in seen]
        print(f"FAIL: only {len(seen)}/{len(decls)} declaration blocks found; missing: {missing[:10]}")
        return 1
    bad = []
    for name, _, axioms_str in blocks:
        inner = axioms_str[1:-1].strip()
        axioms = frozenset(x.strip() for x in inner.split(",")) if inner else frozenset()
        if not axioms <= ALLOWED:
            bad.append((name, axioms))
    if bad:
        for name, axioms in bad:
            print(f"FAIL: nonstandard axioms for {name}: {sorted(axioms)}")
        return 1
    print(f"axiom audit PASS: {len(seen)}/{len(decls)} declarations, cones ⊆ {sorted(ALLOWED)}")

    # forbidden scan
    violations = []
    for mod in MODULES:
        text = (release / mod).read_text()
        cleaned = strip_comments_and_strings(text)
        for word in FORBIDDEN:
            if re.search(r"\b" + word + r"\b", cleaned):
                violations.append((mod, word))
    if violations:
        for mod, word in violations:
            print(f"FAIL: forbidden token '{word}' in {mod}")
        return 1
    print("forbidden scan PASS: no sorry/axiom/admit/unsafe/native_decide/proof_wanted outside comments/strings")
    return 0


if __name__ == "__main__":
    sys.exit(main())
