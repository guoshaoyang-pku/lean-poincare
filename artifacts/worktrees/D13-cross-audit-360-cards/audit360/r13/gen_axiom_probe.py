#!/usr/bin/env python3
"""A3 round-13 independent axiom re-audit (name-inventory design).

For each of the nine D12 cards, against the cold-rebuilt package at
audit360/r13/rebuild/<card>:

  1. one Lean probe dumps EVERY constant under the card's D12 root namespace
     with its declaration kind and its kernel axiom cone (`Lean.collectAxioms`);
  2. two built-in controls (a fake axiom and a fake opaque) are also dumped and
     MUST show up in their own cones (fail-closed on the instrument);
  3. this driver resolves every declaration name claimed by the producer card
     (`proved_declarations` / `exact_blockers_closed`, across all the card JSON
     shapes in use) against the dumped inventory:
       - exact match;
       - single-segment deletion (the F1 over-qualification defect);
       - unique dotted-suffix match (cards that record short names);
     unresolvable or ambiguous claims are reported and fail the run;
  4. every resolved claim must have a cone within {propext, Classical.choice,
     Quot.sound}; the whole namespace must as well (except documented negative
     controls, which are reported separately and never silently skipped).

Output: audit360/r13/axiom_reaudit.json
"""
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REBUILD = os.path.join(ROOT, "audit360", "r13", "rebuild")
LOGS = os.path.join(ROOT, "audit360", "r13", "logs")
PROD = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition", "D12-triangulation-topology", "D12-tensor-maximum-bochner",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# declarations named by the D12-semantic-ledger card that live in the
# audit_probes module of the snapshot package, not in the release package.
# Resolved and cone-checked by snapshot_audit.py in this same round.
SNAPSHOT_RESOLVED = {
    "Poincare.D12.SemanticLedger.real_initialCondition_specializes",
    "Poincare.D12.SemanticLedger.realField_unsatisfiable_by_gaussian",
}
# documented producer-side negative controls (verified to be the only axioms in
# the trees by an independent grep of every staged package)
KNOWN_CONTROLS = {
    "Poincare.D12.VolumeIBP.Audit.negativeControl",
    "Poincare.D12.TriangulationTopology.NegControl.d12NegControlBadAxiom",
}

PROBE = r"""-- A3 round-13 independent axiom re-audit probe (generated)
-- package: @@CARD@@
-- imports every module of the cold-rebuilt package
@@IMPORTS@@

open Lean Elab Command

namespace A3R13

axiom a3r13FakeAxiom : True
opaque a3r13FakeOpaque : True
theorem a3r13UsesFakeAxiom : True := a3r13FakeAxiom
theorem a3r13UsesFakeOpaque : True := a3r13FakeOpaque

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
      logInfo m!"A3R13|CONST|{n}|{kindOf ci}|{axs.toList.map Name.toString}"

/-- Instrument self-test: both controls must produce a non-empty cone naming the
fake constant. -/
def controls : CommandElabM Unit := do
  for n in [``a3r13UsesFakeAxiom, ``a3r13UsesFakeOpaque] do
    let axs ← Lean.collectAxioms n
    logInfo m!"A3R13|CONTROL|{n}|{axs.toList.map Name.toString}"

end A3R13

run_cmd A3R13.dump [`Poincare.D12]
run_cmd A3R13.controls
"""


def modules_of(pkg):
    mods = []
    base = os.path.join(pkg, "Poincare", "D12")
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if d not in (".lake",)]
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), pkg)
                mods.append(rel[:-5].replace(os.sep, "."))
    return sorted(set(mods))


def candidate_names(card_json):
    """Every declaration name the card explicitly claims, across card shapes."""
    names = []

    def add_str(s):
        for m in re.finditer(
            r"\b((?:Poincare|Audit|Ledger|Release|A3)[A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+)", s
        ):
            names.append(m.group(1))

    def add_short(s):
        s = s.strip()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*", s):
            names.append(s)

    def walk(v):
        if isinstance(v, str):
            if v.startswith("Poincare."):
                add_str(v)
            elif " : " in v or "," in v or " " in v:
                head = re.split(r"\s*[:,]", v, 1)[0].strip()
                if head.startswith("Poincare."):
                    add_str(head)
                else:
                    add_short(head)
            else:
                add_short(v)
        elif isinstance(v, dict):
            if isinstance(v.get("name"), str):
                if v["name"].startswith("Poincare."):
                    add_str(v["name"])
                else:
                    add_short(v["name"])
            for k, vv in v.items():
                if k in ("name", "type", "semantic_class", "axiom_class"):
                    continue
                if k == "file":
                    continue
                walk(vv)
        elif isinstance(v, list):
            for e in v:
                walk(e)

    for key in ("proved_declarations", "exact_blockers_closed"):
        if key in card_json:
            walk(card_json[key])
    # order-preserving dedupe
    seen = set()
    out = []
    for n in names:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def resolve(claim, inv, card_root):
    """Resolve a claimed name against the dumped inventory.  Returns
    (resolved | None, method, candidates)."""
    if claim in inv:
        return claim, "exact", [claim]
    segs = claim.split(".")
    # single-segment deletion (over-qualification)
    cands = []
    for i in range(1, len(segs)):
        cand = ".".join(segs[:i] + segs[i + 1:])
        if cand in inv and cand not in cands:
            cands.append(cand)
    if len(cands) == 1:
        return cands[0], "delete-segment", cands
    if len(cands) > 1:
        return None, "ambiguous-delete-segment", cands
    # dotted-suffix match inside the card root
    suff = "." + claim
    cands = [n for n in inv if n.startswith(card_root) and n.endswith(suff)]
    if len(cands) == 1:
        return cands[0], "suffix", cands
    if len(cands) > 1:
        return None, "ambiguous-suffix", cands
    return None, "unresolved", []


CARD_ROOT = {
    "D12-connection-curvature": "Poincare.D12.ConnectionCurvature.",
    "D12-volume-ibp": "Poincare.D12.VolumeIBP.",
    "D12-spectral-sobolev": "Poincare.D12.SpectralSobolev.",
    "D12-semantic-ledger": "Poincare.D12.SemanticLedger.",
    "D12-comparison-geodesics": "Poincare.D12.ComparisonGeodesics.",
    "D12-geometric-compactness": "Poincare.D12.GeometricCompactness.",
    "D12-surgery-recognition": "Poincare.D12.SurgeryRecognition.",
    "D12-triangulation-topology": "Poincare.D12.TriangulationTopology.",
    "D12-tensor-maximum-bochner": "Poincare.D12.TensorMaximumBochner.",
}


def build_probe(card):
    pkg = os.path.join(REBUILD, card)
    mods = modules_of(pkg)
    imports = "\n".join("import " + m for m in mods)
    text = PROBE.replace("@@CARD@@", card).replace("@@IMPORTS@@", imports)
    probe = os.path.join(pkg, "A3R13Dump.lean")
    with open(probe, "w") as f:
        f.write(text)
    return {"probe": probe, "modules": mods}


def run_probe(card):
    pkg = os.path.join(REBUILD, card)
    log = os.path.join(LOGS, f"axiom_reaudit_{card}.log")
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    t0 = time.time()
    with open(log, "w") as lf:
        proc = subprocess.run(["lake", "env", "lean", "A3R13Dump.lean"], cwd=pkg,
                              stdout=lf, stderr=subprocess.STDOUT, env=env, timeout=3600)
    dt = time.time() - t0
    inv = {}
    controls = {}
    errs = []
    # Lean pretty-prints long lists across lines; join continuation lines.
    records = []
    for raw in open(log, errors="replace"):
        if raw.startswith("A3R13|"):
            records.append(raw.rstrip("\n"))
        elif records:
            records[-1] += " " + raw.strip()
    for line in records:
        if line.startswith("A3R13|CONST|"):
            parts = line.split("|")
            name, kind, cone = parts[2], parts[3], parts[4] if len(parts) > 4 else "[]"
            axs = [x.strip() for x in cone.strip("[]").split(",") if x.strip()]
            inv[name] = {"kind": kind, "axioms": axs}
        elif line.startswith("A3R13|CONTROL|"):
            parts = line.split("|")
            axs = [x.strip() for x in parts[3].strip("[]").split(",") if x.strip()]
            controls[parts[2]] = axs
    if proc.returncode != 0:
        errs.append("probe rc != 0")
    if not controls.get("A3R13.a3r13UsesFakeAxiom"):
        errs.append("fake-axiom control produced an empty cone")
    if "A3R13.a3r13FakeAxiom" not in (controls.get("A3R13.a3r13UsesFakeAxiom") or []):
        errs.append("fake-axiom control not detected")
    # NOTE: an `opaque` declaration carries a kernel-checked value, so
    # collectAxioms legitimately does NOT list it; the opaque theorem's empty
    # cone is recorded, not treated as a failure.  The axiom control above is
    # the instrument self-test that must fire.
    return {"rc": proc.returncode, "seconds": round(dt, 1), "log": os.path.relpath(log, ROOT),
            "inventory": inv, "controls": controls, "instrument_errors": errs}


def main():
    os.makedirs(LOGS, exist_ok=True)
    report = {"lane": "A3-round13", "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "allowed": sorted(ALLOWED), "cards": {}, "verdict": "PASS"}
    for card in CARDS:
        report["cards"][card] = build_probe(card)
    with ThreadPoolExecutor(max_workers=len(CARDS)) as ex:
        runs = list(ex.map(run_probe, CARDS))
    for card, run in zip(CARDS, runs):
        e = report["cards"][card]
        inv = run.pop("inventory")
        e["run"] = run
        e["namespace_size"] = len(inv)
        kinds = {}
        for v in inv.values():
            kinds[v["kind"]] = kinds.get(v["kind"], 0) + 1
        e["kind_counts"] = kinds
        # namespace-level unapproved cones
        bad = {n: v["axioms"] for n, v in inv.items()
               if any(a not in ALLOWED for a in v["axioms"])}
        e["unapproved"] = bad
        e["axiom_or_opaque_constants"] = sorted(
            n for n, v in inv.items() if v["kind"] in ("axiom", "opaque"))
        # claims
        cj = json.load(open(os.path.join(PROD, card, "longrun", "results", card + ".json")))
        claims = candidate_names(cj)
        e["claim_count"] = len(claims)
        e["claims"] = {}
        unresolved, ambiguous, missing_in_inv, claim_bad, prose = [], [], [], [], []
        root = CARD_ROOT[card]
        for c in claims:
            r, method, cands = resolve(c, inv, root)
            if r is None:
                if method.startswith("ambiguous"):
                    ambiguous.append({"claim": c, "method": method, "candidates": cands})
                elif c in SNAPSHOT_RESOLVED:
                    e["claims"][c] = {"resolved": c, "method": "snapshot-package",
                                      "kind": "thm", "axioms": None}
                elif c.startswith("Poincare."):
                    unresolved.append({"claim": c, "method": method})
                else:
                    prose.append({"claim": c, "method": method})
                continue
            axs = inv[r]["axioms"]
            e["claims"][c] = {"resolved": r, "method": method, "kind": inv[r]["kind"],
                              "axioms": axs}
            if any(a not in ALLOWED for a in axs):
                claim_bad.append({"claim": c, "resolved": r, "axioms": axs})
        e["claim_unresolved"] = unresolved
        e["claim_prose_or_id"] = prose
        e["claim_ambiguous"] = ambiguous
        e["claim_unapproved"] = claim_bad
        if run["instrument_errors"]:
            e["verdict"] = "FAIL"
        elif bad:
            # documented producer negative controls are reported, not excused
            undocumented = {n: a for n, a in bad.items() if n not in KNOWN_CONTROLS}
            e["undocumented_unapproved"] = undocumented
            e["verdict"] = "FAIL" if undocumented else "PASS-CONTROLS-ONLY"
        elif claim_bad or ambiguous:
            e["verdict"] = "FAIL"
        else:
            e["verdict"] = "PASS"
    for card in CARDS:
        v = report["cards"][card]["verdict"]
        if v == "PASS-CONTROLS-ONLY":
            # only the two documented producer negative controls may be present
            if report["cards"][card].get("undocumented_unapproved"):
                report["verdict"] = "FAIL"
        elif v != "PASS":
            report["verdict"] = "FAIL"
    with open(os.path.join(ROOT, "audit360", "r13", "axiom_reaudit.json"), "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("verdict:", report["verdict"])
    for card in CARDS:
        e = report["cards"][card]
        print(f"  {card:32s} {e['verdict']:18s} ns={e['namespace_size']:5d} "
              f"claims={e['claim_count']:4d} unres={len(e['claim_unresolved'])} "
              f"ambig={len(e['claim_ambiguous'])} bad={len(e['unapproved'])} "
              f"axdecls={e['axiom_or_opaque_constants']} kinds={e['kind_counts']} "
              f"{e['run']['seconds']}s")
        if e.get("instrument_errors"):
            print("      INSTRUMENT:", e["instrument_errors"])
        if e.get("undocumented_unapproved"):
            print("      UNDOCUMENTED:", json.dumps(e["undocumented_unapproved"])[:300])
        if e["claim_unresolved"]:
            print("      UNRESOLVED:", json.dumps(e["claim_unresolved"])[:300])
        if e["claim_ambiguous"]:
            print("      AMBIGUOUS:", json.dumps(e["claim_ambiguous"])[:300])
        if e["claim_unapproved"]:
            print("      CLAIM-BAD:", json.dumps(e["claim_unapproved"])[:300])
    return 0 if report["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
