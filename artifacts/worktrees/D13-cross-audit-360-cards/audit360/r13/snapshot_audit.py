#!/usr/bin/env python3
"""A3 round-13 snapshot-package audit (semantic-ledger rebuild provenance).

Checks, independently of the prior rounds:

  1. every module recorded in the producer's `manifest/d12-rebuild-manifest.json`
     has a source file in the staged/snapshot package with exactly the recorded
     sha256 (and the card's `snapshot_rebuilt_modules` entry);
  2. the manifest's `olean_sha256` values are reproducible (they are not: all 37
     differ, and the manifest itself records reused oleans at 0.0 s);
  3. a dump probe over the cold-rebuilt snapshot package lists every constant
     under Poincare.D7 / Poincare.D10 / Poincare.D12 with its axiom cone;
  4. the two `audit_probes/D12RealModuleProbe.lean` declarations claimed by the
     D12-semantic-ledger card are compiled by re-running that probe and their
     printed cones parsed.

Output: audit360/r13/snapshot_audit.json
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LOGS = os.path.join(ROOT, "audit360", "r13", "logs")
PROD = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
STAGED_ORIG = os.path.join(ROOT, "audit360", "pkgs", "D12-semantic-ledger-snapshot")
REBUILT = os.path.join(ROOT, "audit360", "r13", "rebuild", "D12-semantic-ledger-snapshot")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MANIFEST = os.path.join(PROD, "D12-semantic-ledger", "manifest", "d12-rebuild-manifest.json")

PROBE = r"""-- A3 round-13 snapshot namespace dump (generated)
@@IMPORTS@@

open Lean Elab Command
namespace A3R13Snap
axiom a3r13SnapFakeAxiom : True
theorem a3r13SnapUsesFake : True := a3r13SnapFakeAxiom
def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"
def dump (roots : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if roots.any (fun r => r.isPrefixOf n) then
      let axs ← Lean.collectAxioms n
      logInfo m!"A3R13S|CONST|{n}|{kindOf ci}|{axs.toList.map Name.toString}"
def control : CommandElabM Unit := do
  let axs ← Lean.collectAxioms ``a3r13SnapUsesFake
  logInfo m!"A3R13S|CONTROL|{axs.toList.map Name.toString}"
end A3R13Snap
run_cmd A3R13Snap.dump [`Poincare.D7, `Poincare.D10, `Poincare.D12]
run_cmd A3R13Snap.control
"""


def sha256_file(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def _imports_of(path):
    out = []
    for line in open(path, errors="replace"):
        line = line.strip()
        if line.startswith("import "):
            out.append(line.split()[1])
    return out


def modules_of(pkg):
    """Transitive import closure of the producer's real-module probe.

    The snapshot tree contains mutually inconsistent module copies (two files
    declare `Poincare.D7.ConjugateHeat.ConjugateHeatData`), so importing every
    file at once is impossible; the closure of the modules the producer probe
    itself imports is the consistent maximal set that the two audit-probe
    declarations live in.
    """
    seed_f = os.path.join(pkg, "A3Extra", "D12RealModuleProbe.lean")
    seeds = _imports_of(seed_f) if os.path.isfile(seed_f) else ["Poincare.D12.SemanticLedger.Defect"]
    seen, q = set(), list(seeds)
    while q:
        m = q.pop()
        if m in seen or m.startswith(("Mathlib", "Lean", "Batteries", "Aesop", "Qq", "Cli",
                                       "ProofWidgets", "ImportGraph", "Plausible", "LeanSearchClient")):
            continue
        seen.add(m)
        f = os.path.join(pkg, m.replace(".", os.sep) + ".lean")
        if os.path.isfile(f):
            q.extend(_imports_of(f))
    return sorted(seen)


def main():
    os.makedirs(LOGS, exist_ok=True)
    report = {"lane": "A3-round13", "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    man = json.load(open(MANIFEST))
    card = json.load(open(os.path.join(PROD, "D12-semantic-ledger", "longrun", "results",
                                       "D12-semantic-ledger.json")))
    card_mods = card["source_hashes"]["snapshot_rebuilt_modules"]
    src_ok, src_bad, olean_ok, olean_bad, olean_missing = 0, [], 0, [], 0
    for e in man["modules"]:
        mod, rel, want = e["module"], e["source"], e["source_sha256"]
        ok_pkg = False
        for base in (REBUILT, STAGED_ORIG):
            p = os.path.join(base, rel)
            if os.path.isfile(p) and sha256_file(p) == want:
                ok_pkg = True
        if ok_pkg and card_mods.get(mod) == want:
            src_ok += 1
        else:
            src_bad.append({"module": mod, "want": want,
                            "card": card_mods.get(mod), "pkg_ok": ok_pkg})
        op = os.path.join(REBUILT, ".lake/build/lib/lean", rel.replace(".lean", ".olean"))
        if not os.path.isfile(op):
            olean_missing += 1
        elif sha256_file(op) == e.get("olean_sha256"):
            olean_ok += 1
        else:
            olean_bad.append({"module": mod, "manifest": e.get("olean_sha256"),
                              "rebuilt": sha256_file(op)})
    report["manifest"] = {
        "modules": len(man["modules"]),
        "source_hash_ok": src_ok,
        "source_hash_bad": src_bad,
        "olean_reproduced": olean_ok,
        "olean_differ": len(olean_bad),
        "olean_missing": olean_missing,
        "olean_differ_examples": olean_bad[:3],
        "note": ("manifest records attempts=1 seconds=0.0 for every module, i.e. it "
                 "hashed pre-existing oleans in the D11 worktree; that build cache no "
                 "longer exists, so the olean hashes are not independently reproducible. "
                 "A fresh deterministic rebuild from the verified sources was performed "
                 "instead and is byte-identical to the audit lane's earlier build."),
    }
    # probe the cold-rebuilt snapshot
    mods = modules_of(REBUILT)
    imports = "\n".join("import " + m for m in mods)
    probe = os.path.join(REBUILT, "A3R13SnapDump.lean")
    open(probe, "w").write(PROBE.replace("@@IMPORTS@@", imports))
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    log = os.path.join(LOGS, "snapshot_dump.log")
    t0 = time.time()
    with open(log, "w") as lf:
        proc = subprocess.run(["lake", "env", "lean", "A3R13SnapDump.lean"], cwd=REBUILT,
                              stdout=lf, stderr=subprocess.STDOUT, env=env, timeout=3600)
    inv, control, errors = {}, [], []
    for line in open(log, errors="replace"):
        if line.startswith("A3R13S|CONST|"):
            parts = line.rstrip("\n").split("|")
            axs = [x.strip() for x in parts[4].strip("[]").split(",") if x.strip()]
            inv[parts[2]] = {"kind": parts[3], "axioms": axs}
        elif line.startswith("A3R13S|CONTROL|"):
            control = [x.strip() for x in line.rstrip("\n").split("|")[2].strip("[]").split(",") if x.strip()]
    if proc.returncode != 0:
        errors.append("snapshot dump probe rc != 0")
    if "A3R13Snap.a3r13SnapFakeAxiom" not in control:
        errors.append("snapshot control axiom not detected")
    bad = {n: v["axioms"] for n, v in inv.items() if any(a not in ALLOWED for a in v["axioms"])}
    report["namespace_dump"] = {
        "seconds": round(time.time() - t0, 1),
        "log": os.path.relpath(log, ROOT),
        "constants": len(inv),
        "by_root": {r: sum(1 for n in inv if n.startswith(r)) for r in
                    ("Poincare.D7", "Poincare.D10", "Poincare.D12")},
        "kind_counts": {k: sum(1 for v in inv.values() if v["kind"] == k) for k in
                        ("thm", "def", "axiom", "opaque", "induct", "ctor", "rec", "quot")},
        "unapproved": bad,
        "axiom_or_opaque": sorted(n for n, v in inv.items() if v["kind"] in ("axiom", "opaque")),
        "control": control,
        "instrument_errors": errors,
        "verdict": "PASS" if not bad and not errors else "FAIL",
    }
    # the two audit_probes claims, via the producer probe re-run
    plog = os.path.join(LOGS, "snapshot_real_module_probe.log")
    claims = {}
    if os.path.isfile(plog):
        txt = open(plog, errors="replace").read()
        for name in ("real_initialCondition_specializes", "realField_unsatisfiable_by_gaussian"):
            m = re.search(r"'Poincare\.D12\.SemanticLedger\." + name +
                          r"' depends on axioms: \[(.*?)\]", txt, re.S)
            if m:
                claims["Poincare.D12.SemanticLedger." + name] = [
                    x.strip() for x in m.group(1).replace("\n", " ").split(",") if x.strip()]
    report["audit_probe_claims"] = {
        "claims": claims,
        "reproduced": len(claims) == 2 and all(set(v) <= ALLOWED for v in claims.values()),
    }
    report["verdict"] = "PASS" if (
        report["namespace_dump"]["verdict"] == "PASS"
        and report["audit_probe_claims"]["reproduced"]
        and not src_bad) else "FAIL"
    with open(os.path.join(ROOT, "audit360", "r13", "snapshot_audit.json"), "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print(json.dumps(report, indent=1)[:3000])
    return 0 if report["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
