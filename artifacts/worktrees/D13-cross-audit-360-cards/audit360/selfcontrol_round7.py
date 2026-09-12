#!/usr/bin/env python3
"""Round-7 audit-of-the-auditor POSITIVE controls.

Every earlier round validated the audit pipeline with a *negative control*
(a standalone file containing `sorry` / `native_decide`, checked to be flagged).
That proves the cone predicate rejects bad cones, but not that the pipeline
actually reaches a bad declaration that sits *inside* a card package and is
reached through the card's generated probe / full-namespace audit.

This script closes that gap by injecting defects into throwaway copies of a real
staged card package (`D12-semantic-ledger`, the smallest one) and re-running the
same predicate code used for the real audit:

  C1  an unapproved axiom + a theorem using it      -> probe cone predicate must
                                                       flag it; A3FullAudit must
                                                       report A3FULL-BAD and fail
  C2  a theorem proved by `sorry`                   -> probe cone predicate must
                                                       flag `sorryAx`
  C3  a hypothesis-equals-conclusion tautology      -> vacuity screen T9/T10 must
                                                       flag it
  C4  forbidden-token scanner                       -> must flag `axiom`/`sorry`
  C0  the identical uninjected copy                 -> must pass all four

Nothing here is evidence about the real cards; it is evidence about the audit
tooling.  Injections live only under `audit360/ctl-round7/` and are never part
of any audited package or recorded source hash.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import analyze  # noqa: E402
import vacuity_screen3  # noqa: E402

BASE = os.path.dirname(HERE)
CTL = os.path.join(HERE, "ctl-round7")
SHARED = "/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages"
SRC = os.path.join(HERE, "pkgs", "D12-semantic-ledger")
ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")

CTL_LEAN = """import Poincare.D12.SemanticLedger.LedgerProbe

/-! Round-7 audit self-control: deliberately defective declarations.
This file exists only in a throwaway copy and is never evidence about a card. -/

namespace Poincare
namespace D12
namespace SemanticLedger

axiom a3CtlAxiom : False

theorem a3CtlAxiomTheorem : False := a3CtlAxiom

theorem a3CtlSorryTheorem : False := by
  sorry

theorem a3CtlTauto (P : Prop) (h : P) : P := h

end SemanticLedger
end D12
end Poincare
"""


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def sh(cmd, cwd, timeout=3600):
    cp = subprocess.run(cmd, cwd=cwd, env=ENV, capture_output=True, text=True,
                        timeout=timeout)
    return cp.returncode, cp.stdout + cp.stderr


def make_copy(dst):
    shutil.rmtree(dst, ignore_errors=True)
    os.makedirs(dst)
    subprocess.run(
        f"cd {SRC} && tar cf - --exclude=.lake . | (cd {dst} && tar xf -)",
        shell=True, check=True)
    os.makedirs(os.path.join(dst, ".lake"), exist_ok=True)
    link = os.path.join(dst, ".lake", "packages")
    if not os.path.exists(link):
        os.symlink(SHARED, link)


def inject(dst):
    """Add the defective module and wire it into the card's own probe/audit."""
    rel = os.path.join("Poincare", "D12", "SemanticLedger", "A3Ctl.lean")
    with open(os.path.join(dst, rel), "w") as f:
        f.write(CTL_LEAN)
    # real generated probe + real full-namespace audit, plus the injected module
    for fn in ("A3Probe.lean", "A3FullAudit.lean"):
        p = os.path.join(dst, fn)
        lines = open(p).read().splitlines()
        last_import = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines.insert(last_import + 1, "import Poincare.D12.SemanticLedger.A3Ctl")
        open(p, "w").write("\n".join(lines) + "\n")
    with open(os.path.join(dst, "A3Probe.lean"), "a") as f:
        f.write("""
#check Poincare.D12.SemanticLedger.a3CtlAxiomTheorem
#print axioms Poincare.D12.SemanticLedger.a3CtlAxiomTheorem
#check Poincare.D12.SemanticLedger.a3CtlSorryTheorem
#print axioms Poincare.D12.SemanticLedger.a3CtlSorryTheorem
#check Poincare.D12.SemanticLedger.a3CtlTauto
#print axioms Poincare.D12.SemanticLedger.a3CtlTauto
""")


def probe_types(log_text):
    """Parse `#check` output types keyed by fq name (vacuity_screen3 format)."""
    out, cur, buf = {}, None, []
    for raw in log_text.splitlines():
        line = raw.rstrip("\n")
        if line.startswith("###") or line.startswith("'") or "depends on axioms" in line:
            continue
        m = vacuity_screen3.DECL_START.match(line)
        if m and not line.startswith("  "):
            if cur is not None:
                out[cur] = " ".join(buf).strip()
            cur, buf = m.group(1), [line]
        elif cur is not None:
            buf.append(line)
    if cur is not None:
        out[cur] = " ".join(buf).strip()
    return out


def one(name, path):
    """Build a copy, run its real probe and full audit, and judge with the
    production predicates."""
    rec = {"name": name, "path": path}
    rc, out = sh(["lake", "build"], path, timeout=7200)
    rec["build_rc"] = rc
    open(os.path.join(HERE, f"ctl-round7/{name}.build.log"), "w").write(out)
    rc, out = sh(["lake", "env", "lean", "A3Probe.lean"], path, timeout=3600)
    rec["probe_rc"] = rc
    logp = os.path.join(HERE, f"ctl-round7/{name}.probe.log")
    open(logp, "w").write(out)
    parsed = analyze.parse_probe(logp)
    cones = parsed["cones"]
    violations = {n: c for n, c in cones.items() if not set(c).issubset(analyze.ALLOWED)}
    rec["probe_cones"] = cones
    rec["probe_errors"] = parsed["errors"][:5]
    rec["cone_violations"] = violations
    rec["violation_count"] = len(violations)
    # full-namespace audit (the real one, with the injected import in the inject copy)
    rc, out = sh(["lake", "env", "lean", "A3FullAudit.lean"], path, timeout=3600)
    rec["fullaudit_rc"] = rc
    open(os.path.join(HERE, f"ctl-round7/{name}.fullaudit.log"), "w").write(out)
    rec["fullaudit_bad_lines"] = [l for l in out.splitlines() if "A3FULL-BAD" in l]
    rec["fullaudit_pass_line"] = [l for l in out.splitlines() if "A3FULL: PASS" in l]
    # forbidden-token scan (production scanner)
    hits = analyze.scan_forbidden(path, extra_exclude=("A3Probe.lean", "A3Extra"))
    rec["forbidden_hits"] = hits
    # vacuity screen on the control type
    types = probe_types(open(logp).read())
    tauto = types.get("Poincare.D12.SemanticLedger.a3CtlTauto")
    if tauto:
        fl, binders, concl = vacuity_screen3.flags("Poincare.D12.SemanticLedger.a3CtlTauto", tauto)
        rec["tauto_type"] = tauto[:300]
        rec["tauto_flags"] = fl
    else:
        rec["tauto_type"] = None
        rec["tauto_flags"] = []
    rec["probe_log_sha256"] = sha256(logp)
    return rec


def main():
    os.makedirs(CTL, exist_ok=True)
    clean = os.path.join(CTL, "clean")
    inj = os.path.join(CTL, "inject")
    make_copy(clean)
    make_copy(inj)
    inject(inj)
    report = {
        "schema": "a3-audit-selfcontrol-v1",
        "purpose": ("positive controls: the production probes/scanners must flag injected "
                    "defects inside a real card package, and must not flag the clean copy"),
        "injected_module_sha256": sha256(os.path.join(inj, "Poincare", "D12",
                                                      "SemanticLedger", "A3Ctl.lean")),
        "source_package": SRC,
        "controls": {},
    }
    report["controls"]["C0-clean"] = one("C0-clean", clean)
    report["controls"]["C1C2C3-inject"] = one("C1C2C3-inject", inj)

    c0, c1 = report["controls"]["C0-clean"], report["controls"]["C1C2C3-inject"]
    checks = {
        "C0_build_ok": c0["build_rc"] == 0,
        "C0_probe_ok": c0["probe_rc"] == 0 and c0["violation_count"] == 0,
        "C0_fullaudit_pass": c0["fullaudit_rc"] == 0 and bool(c0["fullaudit_pass_line"]),
        "C0_no_vacuity_flag": not c0["tauto_flags"],
        "C0_forbidden_clean": not c0["forbidden_hits"],
        "C1_axiom_cone_flagged": any("a3CtlAxiom" in a for c in c1["cone_violations"].values()
                                     for a in c),
        "C2_sorry_cone_flagged": any("sorryAx" in a for c in c1["cone_violations"].values()
                                     for a in c),
        "C1_fullaudit_fails": (c1["fullaudit_rc"] != 0
                               and any("a3CtlAxiomTheorem" in l for l in c1["fullaudit_bad_lines"])),
        "C3_tautology_flagged": any(f.startswith(("T9-", "T10-")) for f in c1["tauto_flags"]),
        "C4_forbidden_flagged": (any(h["token"] == "axiom" for h in c1["forbidden_hits"])
                                 and any(h["token"] == "sorry" for h in c1["forbidden_hits"])),
    }
    report["checks"] = checks
    report["all_controls_pass"] = all(checks.values())
    with open(os.path.join(HERE, "selfcontrol_round7.json"), "w") as f:
        json.dump(report, f, indent=1)
    for k, v in checks.items():
        print(("PASS " if v else "FAIL ") + k)
    print("ALL CONTROLS PASS:", report["all_controls_pass"])
    return 0 if report["all_controls_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
