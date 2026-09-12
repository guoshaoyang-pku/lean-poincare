#!/usr/bin/env python3
"""Fail-closed audit-coverage check.

Three sets must agree exactly:

1. `AUTHORS`   — every declaration discovered in the authored adapter sources
                 (comment-stripped; the discovery refuses forms it cannot name);
2. `AUDITED`   — every `#print axioms <name>` in the generated `Audit.lean`
                 modules (and no duplicates / stale names);
3. `LOGGED`    — every record actually printed in the audit log run by
                 `lake env lean <lib>/Audit.lean`.

A declaration added without regenerating the audit, a stale audit name, a
duplicated line, or a truncated/rewritten log all fail here with exit 1.  This
is what makes the axiom audit *fail closed on coverage*, not only on the cones
that happen to be printed.

Usage: check-audit-coverage.py <worktree-root> <audit-log>
"""
import re
import sys
from importlib.machinery import SourceFileLoader
from pathlib import Path

HERE = Path(__file__).resolve().parent
mk = SourceFileLoader("makeaudit", str(HERE / "make-audit-file.py")).load_module()

RECORD = re.compile(
    r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
    re.S,
)


def main():
    root = Path(sys.argv[1]).resolve()
    log = Path(sys.argv[2])
    decls, _ = mk.discover(root / "adapters")
    authors = [d["name"] for d in decls]
    authors_set = set(authors)
    audited_all = mk.audit_lines_of(root)
    audited_set = set(audited_all)
    text = log.read_text(errors="replace")
    logged = [m.group(1) for m in RECORD.finditer(text)]
    logged_set = set(logged)

    problems = []
    dup_decl = sorted({n for n in authors if authors.count(n) > 1})
    dup_audit = sorted({n for n in audited_all if audited_all.count(n) > 1})
    if dup_decl:
        problems.append(f"duplicate authored declarations: {dup_decl}")
    if dup_audit:
        problems.append(f"duplicate audit lines: {dup_audit}")
    missing_audit = sorted(authors_set - audited_set)
    stale_audit = sorted(audited_set - authors_set)
    if missing_audit:
        problems.append("authored declarations with NO audit line "
                        f"({len(missing_audit)}): {missing_audit}")
    if stale_audit:
        problems.append("audit lines with no authored declaration "
                        f"({len(stale_audit)}): {stale_audit}")
    missing_log = sorted(audited_set - logged_set)
    extra_log = sorted(logged_set - audited_set)
    if missing_log:
        problems.append("audit lines with NO record in the log "
                        f"({len(missing_log)}): {missing_log}")
    if extra_log:
        problems.append(f"log records not requested by any audit line: {extra_log}")
    if len(logged) != len(logged_set):
        problems.append("the audit log contains duplicate records")
    if len(audited_all) != len(logged):
        problems.append(f"audit lines ({len(audited_all)}) != log records ({len(logged)})")

    print(f"coverage: {len(authors_set)} authored declarations, "
          f"{len(audited_set)} audit lines, {len(logged)} log records")
    if problems:
        print("AUDIT-COVERAGE CHECK FAILED (fail-closed):")
        for p in problems:
            print("  -", p)
        return 1
    print("AUDIT-COVERAGE CHECK PASSED: authored == audited == logged")
    return 0


if __name__ == "__main__":
    sys.exit(main())
