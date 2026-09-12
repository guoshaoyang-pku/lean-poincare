#!/usr/bin/env python3
"""D13-critical-path-review — fail-closed evidence driver.

Runs the release package build, the three task-local Lean audits, the intentional
negative-control root and the literal `#print axioms` probe.  Records the exact command,
cwd and exit code for each step, and fails unless every expectation holds.

Usage:  python3 audit-evidence/tools/d13_cp_audit.py
"""
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RELEASE = os.path.join(WT, "release")
LOGS = os.path.join(WT, "audit-evidence", "logs")
os.makedirs(LOGS, exist_ok=True)

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(name, args, expect, contains=(), not_contains=(), cwd=RELEASE):
    log_path = os.path.join(LOGS, name + ".log")
    with open(log_path, "w") as f:
        f.write(f"# cwd: {cwd}\n# cmd: {' '.join(args)}\n")
        f.flush()
        p = subprocess.run(args, cwd=cwd, stdout=f, stderr=subprocess.STDOUT)
    out = open(log_path).read()
    ok = (p.returncode in expect)
    for c in contains:
        if c not in out:
            ok = False
    for c in not_contains:
        if c in out:
            ok = False
    return {"step": name, "cmd": args, "cwd": cwd, "exit": p.returncode,
            "expected_exit": sorted(expect), "ok": ok, "log": os.path.relpath(log_path, WT),
            "contains_ok": all(c in out for c in contains),
            "not_contains_ok": all(c not in out for c in not_contains)}, out


def parse_print_axioms(text):
    """Parse `#print axioms` output, joining wrapped lines."""
    lines = text.splitlines()
    joined = []
    for ln in lines:
        if ln.startswith("'") or not joined:
            joined.append(ln)
        else:
            joined[-1] += " " + ln.strip()
    decls = {}
    for ln in joined:
        m = re.match(r"'([^']+)' (depends on axioms: \[(.*)\]|does not depend on any axioms)", ln)
        if m:
            name = m.group(1)
            ax = [] if m.group(3) is None else [a.strip() for a in m.group(3).split(",") if a.strip()]
            decls[name] = ax
    return decls


def main():
    steps = []
    s, _ = run("00-lake-build", ["lake", "build"], {0})
    steps.append(s)
    s, out = run("01-statement-audit", ["lake", "env", "lean",
                 "Poincare/D13/CriticalPathReview/StatementAudit.lean"], {0},
                 contains=["D13CP_VERDICT\tPASS"])
    steps.append(s)
    s, out = run("02-usage-probe", ["lake", "env", "lean",
                 "Poincare/D13/CriticalPathReview/UsageProbe.lean"], {0},
                 contains=["D13CP_USE_VERDICT\tPASS"])
    steps.append(s)
    s, out = run("03-axiom-audit", ["lake", "env", "lean",
                 "Poincare/D13/CriticalPathReview/AxiomAudit.lean"], {0},
                 contains=["D13CPAUDIT_VERDICT\tPASS"])
    steps.append(s)
    # The negative-control root deliberately FAILS elaboration, so it must live OUTSIDE the
    # release package: the dispatcher's compile gate runs `lake env lean` on every `.lean`
    # file under `release/` and requires exit 0.  cwd stays `release/` so that `lake env`
    # supplies the package LEAN_PATH; the path is relative to that cwd.
    s, out = run("04-negcontrol-included", ["lake", "env", "lean",
                 "../audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean"], {1},
                 contains=["D13CPAUDIT_VERDICT\tFAIL",
                           "Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom"])
    steps.append(s)
    s, out = run("05-print-axioms", ["lake", "env", "lean",
                 "Poincare/D13/CriticalPathReview/PrintAxioms.lean"], {0})
    steps.append(s)
    s, out_all = run("06-print-axioms-all", ["lake", "env", "lean",
                     "Poincare/D13/CriticalPathReview/PrintAxiomsAll.lean"], {0})
    steps.append(s)

    cones = parse_print_axioms(out)
    cones_all = parse_print_axioms(out_all)
    bad = {n: a for n, a in cones.items() if not set(a) <= ALLOWED}
    bad_all = {n: a for n, a in cones_all.items() if not set(a) <= ALLOWED}
    if len(cones) < 20:
        bad["__missing_print_axioms_entries__"] = [f"parsed {len(cones)} declarations"]
    if len(cones_all) < 63:
        bad_all["__missing_print_axioms_all_entries__"] = [f"parsed {len(cones_all)} declarations"]
    steps.append({"step": "07-print-axioms-parse", "declarations": len(cones),
                  "unapproved_cones": bad, "ok": not bad})
    steps.append({"step": "08-print-axioms-all-parse", "declarations": len(cones_all),
                  "unapproved_cones": bad_all, "ok": not bad_all})

    summary = {
        "task_id": "D13-critical-path-review",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "worktree": WT,
        "steps": steps,
        "all_ok": all(x.get("ok", False) for x in steps),
    }
    with open(os.path.join(WT, "audit-evidence", "audit-summary.json"), "w") as f:
        json.dump(summary, f, indent=1)
    with open(os.path.join(WT, "audit-evidence", "transcript.txt"), "w") as f:
        for x in steps:
            f.write(json.dumps(x) + "\n")
    print(json.dumps({"all_ok": summary["all_ok"],
                      "steps": [(x["step"], x.get("exit", "-"), x.get("ok")) for x in steps]},
                     indent=1))
    return 0 if summary["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
