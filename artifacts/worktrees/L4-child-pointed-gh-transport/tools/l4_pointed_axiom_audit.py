#!/usr/bin/env python3
"""Fail-closed audit for task L4-child-pointed-gh-transport.

Checks, in order, and fails closed on any anomaly:

1. `release/Poincare/L4/PointedGH/AxiomAudit.lean` compiles with `lake env lean`
   (exit 0).
2. Every `#print axioms <name>` command in that file is parsed from the output
   (no vacuous or partial parse) and its axiom set is a subset of the allowed
   kernel-trust set {propext, Classical.choice, Quot.sound}.
3. A planted negative control (`axiom l4NegControlAxiom : False` plus a theorem
   consuming it) is run through the same parser and must be flagged; otherwise
   the checker reports that it is not fail-closed.
4. The task's own source files pass a comment/string-aware forbidden-token scan
   for `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`,
   `admit`, `partial`.
5. **No statement-only `Prop` is consumed**: the same comment/string-aware scan
   must find no *code-level* mention of D12's statement-only `Prop`s
   (`harmonicCoordinatesExistence`, `bishopGromovVolumeComparison`,
   `curvatureBoundImpliesUniformCovers`, `cheegerGromovCompactness`,
   `ancientKappaCompactnessFrontier`, `canonicalNeighborhoodFrontier`) in the
   task's sources.  (Mentions inside comments/docstrings are allowed and
   expected: the documentation explains that they are *not* consumed.)

Exit code 0 only if all checks pass.  The JSON report is written to the path
given as the first argument (default `manifest/l4-pointed-gh-audit.json`).

Usage (from the worktree root):
    python3 tools/l4_pointed_axiom_audit.py [report.json]
"""
import json
import os
import re
import subprocess
import sys
import tempfile

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_FILE = "Poincare/L4/PointedGH/AxiomAudit.lean"
TASK_SOURCES = [
    "Poincare/L4/PointedGH/Transport.lean",
    "Poincare/L4/PointedGH/Family.lean",
    "Poincare/L4/PointedGH/Instances.lean",
    "Poincare/L4/PointedGH/AxiomAudit.lean",
]
FORBIDDEN_TOKENS = [
    "sorry", "axiom", "unsafe", "native_decide", "proof_wanted", "sorryAx", "admit", "partial",
]
STATEMENT_ONLY_PROPS = [
    "harmonicCoordinatesExistence",
    "bishopGromovVolumeComparison",
    "curvatureBoundImpliesUniformCovers",
    "cheegerGromovCompactness",
    "ancientKappaCompactnessFrontier",
    "canonicalNeighborhoodFrontier",
]

sys.path.insert(0, os.path.join("input", "d5-tools"))
try:
    from scan_forbidden import strip_comments_and_strings
except Exception as exc:  # pragma: no cover - fail closed
    print(f"[FAIL] cannot import comment stripper: {exc}")
    sys.exit(1)


def parse_axiom_lines(text):
    """Return dict name -> set of axioms from `#print axioms` output lines.

    Lean quotes a name containing a prime as `'Foo''`, so the name group must be
    matched greedily up to the last quote before ` depends on`.
    """
    result = {}
    for m in re.finditer(r"'(.+)' depends on axioms: \[([^\]]*)\]", text):
        name = m.group(1)
        axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
        result[name] = axioms
    return result


def audit_decls(decls, expected, label, report):
    ok = True
    missing = sorted(expected - set(decls))
    if missing:
        print(f"[FAIL] {label}: {len(missing)} declared audits missing from output:")
        for name in missing:
            print(f"  {name}")
        ok = False
    extra = sorted(set(decls) - expected)
    if extra:
        print(f"[WARN] {label}: unexpected parsed names (not declared in the audit file): {extra}")
    bad = []
    for name in sorted(expected & set(decls)):
        extra_ax = decls[name] - ALLOWED
        if extra_ax:
            bad.append((name, sorted(extra_ax)))
    if bad:
        print(f"[FAIL] {label}: forbidden axioms found:")
        for name, ax in bad:
            print(f"  {name}: {ax}")
        ok = False
    if not expected:
        print(f"[FAIL] {label}: no `#print axioms` commands found in the audit file")
        ok = False
    if ok:
        print(f"[OK] {label}: {len(expected)} declarations parsed, axioms ⊆ allowed set")
    report["declarations"] = {
        "expected": sorted(expected),
        "parsed": len(decls),
        "axiom_cones": {k: sorted(v) for k, v in sorted(decls.items())},
        "ok": ok,
    }
    return ok


def source_scan(report):
    ok = True
    forbidden_hits = []
    prop_hits = []
    for rel in TASK_SOURCES:
        path = os.path.join("release", rel)
        if not os.path.exists(path):
            print(f"[FAIL] task source missing: {path}")
            ok = False
            continue
        raw = open(path, encoding="utf-8").read()
        code = strip_comments_and_strings(raw)
        code = re.sub(r"«[^»\n]*»", lambda m: " " * len(m.group(0)), code)
        for tok in FORBIDDEN_TOKENS:
            for m in re.finditer(r"\b" + re.escape(tok) + r"\b", code):
                line = code[: m.start()].count("\n") + 1
                forbidden_hits.append({"file": rel, "token": tok, "line": line})
        for prop in STATEMENT_ONLY_PROPS:
            for m in re.finditer(r"\b" + re.escape(prop) + r"\b", code):
                line = code[: m.start()].count("\n") + 1
                prop_hits.append({"file": rel, "prop": prop, "line": line})
    if forbidden_hits:
        print(f"[FAIL] forbidden tokens in task sources: {forbidden_hits}")
        ok = False
    else:
        print(f"[OK] forbidden-token scan: {len(TASK_SOURCES)} files clean "
              f"(tokens: {FORBIDDEN_TOKENS})")
    if prop_hits:
        print(f"[FAIL] statement-only Props mentioned in code: {prop_hits}")
        ok = False
    else:
        print(f"[OK] statement-only-Prop non-consumption: no code-level mention of "
              f"{STATEMENT_ONLY_PROPS}")
    report["source_scan"] = {
        "files": TASK_SOURCES,
        "forbidden_tokens": FORBIDDEN_TOKENS,
        "forbidden_hits": forbidden_hits,
        "statement_only_props": STATEMENT_ONLY_PROPS,
        "statement_only_prop_code_hits": prop_hits,
        "ok": ok,
    }
    return ok


def main(argv):
    report_path = argv[1] if len(argv) > 1 else "manifest/l4-pointed-gh-audit.json"
    release = "release"
    if not os.path.exists(os.path.join(release, "lakefile.toml")):
        print("[FAIL] run from the worktree root (release/lakefile.toml not found)")
        return 1

    report = {"schema": "l4-child-pointed-gh-transport/audit-v1", "allowed_axioms": sorted(ALLOWED)}
    ok = True

    # 1. compile the audit module and capture its #print axioms output
    proc = subprocess.run(
        ["lake", "env", "lean", AUDIT_FILE], cwd=release, capture_output=True, text=True
    )
    report["audit_module_exit"] = proc.returncode
    if proc.returncode != 0:
        print("[FAIL] audit module does not compile:")
        print(proc.stderr[-4000:])
        report["ok"] = False
        _write(report_path, report)
        return 1
    print("[OK] audit module compiles (exit 0)")

    decls = parse_axiom_lines(proc.stdout)
    expected = set(re.findall(r"^#print axioms (\S+)$", open(
        os.path.join(release, AUDIT_FILE), encoding="utf-8").read(), re.M))
    ok &= audit_decls(decls, expected, "task declarations and consumed D12 theorems", report)

    # 2. negative control: an intentional axiom must be flagged
    with tempfile.TemporaryDirectory() as td:
        neg = os.path.join(td, "L4NegControl.lean")
        with open(neg, "w") as f:
            f.write(
                "import Mathlib.Tactic\n"
                "axiom l4NegControlAxiom : False\n"
                "theorem l4NegControlTheorem : False := l4NegControlAxiom\n"
                "#print axioms l4NegControlTheorem\n"
            )
        proc2 = subprocess.run(
            ["lake", "env", "lean", neg], cwd=release, capture_output=True, text=True
        )
        control = parse_axiom_lines(proc2.stdout)
        flagged = any(ax not in ALLOWED for axs in control.values() for ax in axs)
        report["negative_control"] = {
            "parsed": {k: sorted(v) for k, v in control.items()},
            "detected": flagged,
        }
        if not flagged:
            print("[FAIL] negative control NOT detected: checker is not fail-closed")
            ok = False
        else:
            print(f"[OK] negative control detected (fail-closed confirmed): {control}")

    # 3. source scans
    ok &= source_scan(report)

    report["ok"] = ok
    _write(report_path, report)
    if not ok:
        print("[FAIL] L4-child-pointed-gh-transport audit did not pass")
        return 1
    print("[PASS] L4-child-pointed-gh-transport audit: axiom cones clean, "
          "negative control detected, sources clean")
    return 0


def _write(path, report):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
