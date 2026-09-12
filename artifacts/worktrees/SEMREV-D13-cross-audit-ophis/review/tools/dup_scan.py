#!/usr/bin/env python3
"""Source-level duplicate-declaration inventory for the transported snapshot trees.

Tracks `namespace`/`end` and `section`/`end` to build fully-qualified names for top-level
declarations, then reports any qualified name declared by two different modules.  This is an
independent, mechanical inventory of the in-package name collisions that make a whole-package
single-environment import impossible (the parent card reported one such collision).
"""
import collections
import json
import os
import re
import sys

SNAP = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards/audit/ophis"
REV = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis"

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
                  r"(def|theorem|lemma|structure|inductive|abbrev|class|axiom|opaque|alias)\s+"
                  r"([A-Za-z_\u00ab\u00bb][A-Za-z0-9_'.\u00ab\u00bb!?]*)")
NS = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.'_\u00ab\u00bb]+)")
END = re.compile(r"^\s*end\s*([A-Za-z0-9_.'_\u00ab\u00bb]*)")
SECTION = re.compile(r"^\s*section\s*([A-Za-z0-9_.'_\u00ab\u00bb]*)?")


def strip_comments_strings(s):
    out = []
    i, n, depth, instr = 0, len(s), 0, False
    while i < n:
        if depth > 0:
            if s.startswith("/-", i):
                depth += 1; i += 2; continue
            if s.startswith("-/", i):
                depth -= 1; i += 2; continue
            i += 1; continue
        if instr:
            if s[i] == "\\":
                i += 2; continue
            if s[i] == '"':
                instr = False
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j; continue
        if s.startswith("/-", i):
            depth = 1; i += 2; continue
        if s[i] == '"':
            instr = True; i += 1; continue
        out.append(s[i]); i += 1
    return "".join(out)


def decls_of(path):
    """Return list of fully-qualified declaration names in one file."""
    src = strip_comments_strings(open(path, errors="replace").read())
    names = []
    ns = []
    secs = 0
    for line in src.splitlines():
        m = SECTION.match(line)
        if m and not line.strip().startswith("--"):
            secs += 1
            continue
        m = NS.match(line)
        if m:
            ns.append(m.group(1))
            continue
        m = END.match(line)
        if m:
            if ns:
                ns.pop()
            elif secs:
                secs -= 1
            continue
        m = DECL.match(line)
        if m:
            kind, nm = m.group(1), m.group(2)
            if nm.startswith("_") or nm in ("_",):
                continue
            if kind == "alias":
                continue
            full = ".".join(ns + [nm]) if ns else nm
            names.append((full, kind))
    return names


def main():
    report = {}
    for task in sorted(os.listdir(SNAP)):
        root = f"{SNAP}/{task}/release"
        if not os.path.isdir(root):
            continue
        byname = collections.defaultdict(list)
        for dp, dn, fn in os.walk(root):
            dn[:] = [d for d in dn if d != ".lake"]
            for f in fn:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, root)[:-5].replace("/", ".")
                for full, kind in decls_of(p):
                    byname[full].append((mod, kind))
        dups = {k: v for k, v in byname.items() if len({m for m, _ in v}) > 1}
        report[task] = {
            "duplicate_qualified_names": {
                k: sorted({m for m, _ in v}) for k, v in sorted(dups.items())
            },
            "duplicate_count": len(dups),
        }
        print(f"{task}: duplicate qualified names = {len(dups)}")
        for k, v in sorted(dups.items()):
            print("   ", k, "<-", sorted({m for m, _ in v})[:6])
    with open(f"{REV}/review/evidence/duplicate-names.json", "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
