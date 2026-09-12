#!/usr/bin/env python3
"""Forbidden-token check for the authored adapter files.

Fails if any authored `.lean` file uses `sorry`, `axiom`, `admit`, `unsafe`,
`native_decide` or `proof_wanted` in *code* (comments and string literals are
stripped with the same scanner used for the snapshot inventory, so a docstring
mention does not trip the check).

Usage: check-authored-files.py <worktree-root> [subdir]

`subdir` defaults to `adapters` (the adapter contract: no forbidden token at
all).  Pass `release` to scan a release mirror with the same comment-aware
rules; the release package intentionally contains explicitly labelled
statement-only files, so those hits must be classified, not silently ignored.
"""
import sys
from importlib.machinery import SourceFileLoader
from pathlib import Path

HERE = Path(__file__).resolve().parent
inv = SourceFileLoader("inv2", str(HERE / "inventory-v2.py")).load_module()

import re  # noqa: E402

FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    # `[ \t]*` rather than `\s*`: with re.M, `\s` spans newlines, which would
    # report the start of a blank-line run instead of the `axiom` line.
    "axiom": re.compile(r"^[ \t]*axiom\b", re.M),
    "admit": re.compile(r"\badmit\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "proof_wanted": re.compile(r"\bproof_wanted\b"),
}


def main():
    root = Path(sys.argv[1]).resolve()
    subdir = sys.argv[2] if len(sys.argv) > 2 else "adapters"
    files = sorted(p for p in (root / subdir).rglob("*.lean") if ".lake" not in p.parts)
    failures = []
    for p in files:
        code = inv.strip_comments(p.read_text(errors="replace"))
        for name, rx in FORBIDDEN.items():
            for m in rx.finditer(code):
                line = code[: m.start()].count("\n") + 1
                failures.append(f"{p.relative_to(root)}:{line}: forbidden token `{name}`")
    print(f"checked {len(files)} authored Lean files under {subdir}/")
    for f in failures:
        print("FORBIDDEN:", f)
    if failures:
        print("AUTHORED-FILE CHECK FAILED")
        return 1
    print("AUTHORED-FILE CHECK PASSED: no forbidden tokens in code")
    return 0


if __name__ == "__main__":
    sys.exit(main())
