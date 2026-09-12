#!/usr/bin/env python3
"""Invocation-7 independent, fail-closed axiom audit.

Written from scratch for this invocation; does NOT import tools/l4cp_verify.py.

What it checks, independently:

  A. expected set: the `#print axioms` queries in the audit module source (parsed here)
     equal the declarations found in the raw `lake env lean` audit output;
  B. cones: every parsed cone is a subset of {propext, Classical.choice, Quot.sound} and
     contains no `sorryAx`;
  C. probe: the same predicate over the invocation-7 probe log, and the 15 fresh
     declarations are all present;
  D. negative controls: the real tainted control (sorryAx, declared axiom) and a synthetic
     tainted log are both rejected by the same predicate;
  E. forbidden-token scan of the two authored sources with comments stripped.
"""
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ENDPOINT = ROOT / "release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean"
AUDIT = ROOT / "release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean"
LOG = ROOT / "logs/l4cp-verify-axioms.log"
PROBE = ROOT / "tmp/l4cp_probe_inv7.lean"
PROBE_LOG = ROOT / "logs/l4cp-probe-inv7.log"
NEG_LOG = ROOT / "logs/l4cp-negative-control.log"
NEG_SYN = ROOT / "logs/l4cp-negative-control-synthetic.log"


def strip_comments(text: str) -> str:
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def parse_cones(text: str):
    """Return {name: set(axioms)} for 'X depends on axioms: [...]' and 'X does not depend'."""
    res = {}
    pattern = re.compile(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)",
        re.S)
    for m in pattern.finditer(text):
        name = m.group(1)
        body = m.group(2)
        axioms = set() if body is None else {a.strip() for a in body.split(",") if a.strip()}
        res[name] = axioms
    return res


def check_cones(cones, tag, failures):
    for name, ax in cones.items():
        if "sorryAx" in ax:
            failures.append(f"{tag}: {name} depends on sorryAx")
        bad = ax - ALLOWED
        if bad:
            failures.append(f"{tag}: {name} has disallowed axioms {sorted(bad)}")


def main():
    failures = []
    report = {"generated_at": datetime.now(timezone.utc).isoformat(), "checks": {}}

    # A. expected set from the audit source vs the raw audit log
    expected = set(re.findall(r"^#print axioms (\S+)\s*$", AUDIT.read_text(), re.M))
    audit_log = LOG.read_text()
    found = parse_cones(audit_log)
    report["checks"]["A_expected_count"] = len(expected)
    report["checks"]["A_found_count"] = len(found)
    if expected != set(found):
        failures.append(f"A: expected-only {sorted(expected - set(found))}, "
                        f"found-only {sorted(set(found) - expected)}")

    # B. cones of the audit log
    check_cones(found, "B/audit", failures)
    report["checks"]["B_distinct_cones"] = sorted({tuple(sorted(v)) for v in found.values()})

    # C. probe declarations
    probe_text = PROBE.read_text()
    probe_expected = set(re.findall(
        r"^#print axioms (\S+)\s*$", probe_text, re.M))
    probe_found = parse_cones(PROBE_LOG.read_text())
    report["checks"]["C_probe_expected_count"] = len(probe_expected)
    report["checks"]["C_probe_found_count"] = len(probe_found)
    if probe_expected != set(probe_found):
        failures.append(f"C: probe expected-only {sorted(probe_expected - set(probe_found))}, "
                        f"probe found-only {sorted(set(probe_found) - probe_expected)}")
    check_cones(probe_found, "C/probe", failures)
    report["checks"]["C_new_nonconstant_witness_cone"] = sorted(
        probe_found.get("Poincare.L4.GeodesicComparison.inv7_nonconstant_witness", set()))

    # D. negative controls must be rejected by the same predicate
    neg = parse_cones(NEG_LOG.read_text())
    syn = parse_cones(NEG_SYN.read_text())

    def rejected(cones, tag):
        hits = []
        for name, ax in cones.items():
            if ax - ALLOWED:
                hits.append((name, sorted(ax)))
        report["checks"][f"D_{tag}_rejected"] = hits
        return bool(hits)

    if not rejected(neg, "real"):
        failures.append("D: real negative control was not rejected")
    if not rejected(syn, "synthetic"):
        failures.append("D: synthetic negative control was not rejected")

    # E. forbidden tokens in authored sources (comments stripped)
    forbidden = ["sorry", "admit", "unsafe", "native_decide", "proof_wanted"]
    for path in (ENDPOINT, AUDIT):
        src = strip_comments(path.read_text())
        hits = [tok for tok in forbidden if re.search(rf"\b{tok}\b", src)]
        decl_axiom = re.search(r"^\s*axiom\b", src, re.M)
        if decl_axiom:
            hits.append("axiom-declaration")
        report["checks"][f"E_{path.name}"] = hits
        if hits:
            failures.append(f"E: {path.name} contains {hits}")

    report["failures"] = failures
    report["ok"] = not failures
    print(json.dumps(report, indent=1))
    (ROOT / "logs/l4cp-independent-audit-inv7.log").write_text(json.dumps(report, indent=1) + "\n")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
