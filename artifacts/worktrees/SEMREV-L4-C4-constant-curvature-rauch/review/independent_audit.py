#!/usr/bin/env python3
"""SEMREV-L4-C4 independent replay audit (review worktree).

Reads only the parent artifact (read-only) and the fresh review build/audit logs.
Writes review/independent-audit.json.  Fail-closed: any anomaly sets ok=false.
"""
import hashlib
import json
import os
import re
import sys
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
WS = os.path.dirname(HERE)
PAR = ("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/"
       "L4-C4-constant-curvature-rauch")
L1 = ("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/"
      "leaders/L1-lean-baseline/release")
FRESH_AXIOMS = os.path.join(HERE, "logs", "fresh-axioms.log")

AUTHORED = {
    "release/Poincare/L4/GeodesicComparison/ConstCurvNormalization.lean":
        "84ea042f5038b5dfa77a3487f5ee78eeaf8664abeaee046ba2ddbe8930a8c2cf",
    "release/Poincare/L4/GeodesicComparison/AxiomAudit.lean":
        "7d290ef0b1d80a20dff97c2957798f72bb31a3222ec614fcd95ec6f0ad16ad66",
}
IMPORTED = {
    "release/Poincare/D10/JacobiConstantCurvature/Basic.lean":
        "af126a030be3d08fb553b51faff8ff0840713b5bd9f44344b781e233c86cda40",
    "release/Poincare/D10/JacobiConstantCurvature/ODE.lean":
        "e83ec3c5922d865569b000209e593a284f70bd57127cd226a202abd0df9b2a28",
    "release/Poincare/D10/JacobiConstantCurvature/Comparison.lean":
        "d187e56c2a359aa18c0cd3bf04837e87f48819e9593acf35bd6d273be97b9992",
    "release/Poincare/D12/ComparisonGeodesics/Definitions.lean":
        "62b9637d467cb483890e7e95685ac0beb1e29571892a09d7682d41f06de00dd5",
    "release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean":
        "446605cd23dca7ab1bb29cd036e0c78cd612dc565c5b8d44a0788062e47ef9a8",
}
CONFIG = {
    "release/lakefile.toml":
        "da970151371760d04c15987e8b5cfbe426d835b581da5fba611df9d4473d22e1",
    "release/lean-toolchain":
        "8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88",
    "release/lake-manifest.json":
        "cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0",
}
AUDIT_DECLS = [
    "sin_sub_mul_cos_nonneg", "sin_sub_mul_cos_le_cube", "sphere_logDeriv_bound",
    "jacobiSolSphere_abs_le", "jacobiSolSphere_logDeriv_bound", "jacobiSol_logDeriv_bound",
    "jacobiSol_logDeriv_normalized", "jacobiSol_pos_of_nonneg",
    "jacobiSol_pos_of_nonneg_Ioc", "jacobiSol_riccati_identity",
    "abs_sub_le_of_deriv_bound", "jacobi_linear_bounds", "jacobi_pos_and_ratio_bound",
    "euclideanNormalizedOn_of_jacobi", "jacobi_riccati_identity",
    "logDeriv_continuousOn", "logDeriv_continuousOn_jacobi", "rauch_upper_of_constCurv",
    "rauch_upper_of_constCurv_jacobi", "rauch_upper_flat_of_jacobi",
    "sphere_jacobiSolutionOn_four_oneHalf", "spherical_rauch_witness",
    "spherical_rauch_witness_cot", "jacobiSolOne_normalization_witness",
    "jacobiSolOne_normalized", "flat_model_normalized",
]
AUDIT_ENGINE = ["riccati_le_of_singular_normalization", "riccati_le_of_initial",
                "riccati_delta_le_exp"]
AUDIT_MODEL = ["jacobiSol_ode", "hasDerivAt_jacobiSol", "hasDerivAt_jacobiDeriv",
               "jacobiSolSphere_pos", "continuous_jacobiSol"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [(r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"), (r"\bunsafe\b", "unsafe"),
             (r"\bnative_decide\b", "native_decide"), (r"\bproof_wanted\b", "proof_wanted"),
             (r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*axiom\b",
              "axiom declaration"), (r"\bsorryAx\b", "sorryAx")]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if depth == 0 and text.startswith("/-", i):
            depth, i = 1, i + 2
            out.append("  ")
        elif depth > 0 and text.startswith("/-", i):
            depth, i = depth + 1, i + 2
            out.append("  ")
        elif depth > 0 and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
            out.append("  ")
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    res = {"task": "SEMREV-L4-C4-constant-curvature-rauch",
           "generated_at": datetime.now(timezone.utc).isoformat(), "ok": False,
           "findings": []}

    def fail(msg):
        res["findings"].append({"severity": "BLOCKER", "finding": msg})

    # --- 1. hashes relative to the card and the L1 baseline -------------------------
    hashes = {}
    for rel, want in {**AUTHORED, **IMPORTED, **CONFIG}.items():
        got = sha256(os.path.join(PAR, rel))
        hashes[rel] = {"sha256": got, "card": want, "match": got == want}
        if got != want:
            fail("hash mismatch vs card: %s got %s want %s" % (rel, got, want))
    for rel in IMPORTED:
        got = sha256(os.path.join(PAR, rel))
        base = sha256(os.path.join(L1, rel.split("release/", 1)[1]))
        hashes[rel]["l1_sha256"] = base
        hashes[rel]["l1_identical"] = got == base
        if got != base:
            fail("imported source differs from L1 baseline: %s" % rel)
    res["hashes"] = hashes
    res["gates_hash_and_provenance"] = all(v["match"] for v in hashes.values()) and all(
        hashes[r].get("l1_identical", True) for r in IMPORTED)

    # --- 2. forbidden tokens, comments stripped, all seven sources ------------------
    scan = {}
    for rel in {**AUTHORED, **IMPORTED}:
        clean = strip_comments(open(os.path.join(PAR, rel), encoding="utf-8").read())
        hits = []
        for pat, label in FORBIDDEN:
            for m in re.finditer(pat, clean):
                hits.append({"token": label, "pos": m.start()})
        scan[rel] = hits
        if hits:
            fail("forbidden tokens in %s: %s" % (rel, hits))
    res["forbidden_scan"] = scan
    res["gates_forbidden_clean"] = all(not v for v in scan.values())

    # --- 3. declaration inventory vs audit list -------------------------------------
    l4 = open(os.path.join(PAR, AUTHORED and
              "release/Poincare/L4/GeodesicComparison/ConstCurvNormalization.lean"),
              encoding="utf-8").read()
    clean = strip_comments(l4)
    decls = re.findall(
        r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([A-Za-z_][A-Za-z0-9_']*)",
        clean)
    res["declaration_inventory"] = {"count": len(decls), "names": decls,
                                    "audited_authored": AUDIT_DECLS}
    if sorted(decls) != sorted(AUDIT_DECLS):
        fail("declaration inventory != audited authored list: extra=%s missing=%s" % (
            sorted(set(decls) - set(AUDIT_DECLS)), sorted(set(AUDIT_DECLS) - set(decls))))
    res["gates_inventory_exact"] = sorted(decls) == sorted(AUDIT_DECLS)

    # --- 4. audit query list in AxiomAudit.lean is exactly the expected set ---------
    audit_src = open(os.path.join(
        PAR, "release/Poincare/L4/GeodesicComparison/AxiomAudit.lean"), encoding="utf-8").read()
    queried = re.findall(r"^#print axioms (\S+)\s*$", audit_src, re.M)
    expected_fq = sorted(["Poincare.L4.GeodesicComparison." + d for d in AUDIT_DECLS]
                         + ["Poincare.D12.ComparisonGeodesics." + d for d in AUDIT_ENGINE]
                         + ["Poincare.D10." + d for d in AUDIT_MODEL])
    res["audit_query_list"] = {"queried": len(queried), "expected": len(expected_fq),
                               "exact": sorted(queried) == expected_fq}
    if sorted(queried) != expected_fq:
        fail("audit query list mismatch")

    # --- 5. fail-closed parse of the FRESH audit log --------------------------------
    text = open(FRESH_AXIOMS, encoding="utf-8").read()
    flat = re.sub(r"\n\s+", " ", text)
    cones = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", flat, re.S):
        name = m.group(1)
        cone = [a.strip() for a in m.group(2).split(",") if a.strip()]
        if name in cones:
            fail("duplicate #print axioms entry: %s" % name)
        cones[name] = cone
    by_short = {k.rsplit(".", 1)[-1]: k for k in cones}
    missing = [d for d in (AUDIT_DECLS + AUDIT_ENGINE + AUDIT_MODEL) if d not in by_short]
    bad = {k: c for k, c in cones.items() if not set(c) <= ALLOWED}
    empty_cones = {k: c for k, c in cones.items() if not c}
    no_axiom_lines = len(re.findall(r"does not depend on any axioms", text))
    sorry_hits = len(re.findall(r"sorryAx", text))
    errors = len(re.findall(r"(?m)^(error|Error)", text))
    res["fresh_audit"] = {
        "log": os.path.relpath(FRESH_AXIOMS, WS),
        "parsed": len(cones), "missing": missing, "bad_cones": bad,
        "empty_cones": empty_cones, "does_not_depend_lines": no_axiom_lines,
        "sorryAx_occurrences": sorry_hits, "error_lines": errors,
        "exit_zero_marker": "EXIT=0" in text,
    }
    if missing:
        fail("fresh audit missing declarations: %s" % missing)
    if bad:
        fail("fresh audit bad cones: %s" % bad)
    if sorry_hits or errors or not res["fresh_audit"]["exit_zero_marker"]:
        fail("fresh audit log tainted/erroring")
    res["gates_axioms_fail_closed"] = (not missing and not bad and not sorry_hits
                                       and not errors
                                       and res["fresh_audit"]["exit_zero_marker"])

    # --- 6. reviewed revision -> final revision diff must be comment-only -----------
    rev = open(os.path.join(PAR, "reference/reviewed-revision/"
                                 "ConstCurvNormalization.reviewed.lean"), encoding="utf-8").read()
    fin = l4
    rev_clean, fin_clean = strip_comments(rev), strip_comments(fin)
    same_code = re.sub(r"\s+", " ", rev_clean).strip() == re.sub(r"\s+", " ", fin_clean).strip()
    rev_hash = sha256(os.path.join(PAR, "reference/reviewed-revision/"
                                        "ConstCurvNormalization.reviewed.lean"))
    res["reviewed_revision"] = {
        "reviewed_sha256": rev_hash,
        "card_reviewed_sha256": "05e343a3586609f1df6aef924bd2fa9cba0ae633dacd39a56177d0e34987641e",
        "comment_stripped_identical_to_final": same_code,
    }
    if rev_hash != res["reviewed_revision"]["card_reviewed_sha256"]:
        fail("reviewed-revision hash mismatch")
    if not same_code:
        fail("post-review diff is not comment-only")

    res["ok"] = (res["gates_hash_and_provenance"] and res["gates_forbidden_clean"]
                 and res["gates_inventory_exact"] and res["gates_axioms_fail_closed"]
                 and same_code and not any(f["severity"] == "BLOCKER"
                                           for f in res["findings"]))
    with open(os.path.join(HERE, "independent-audit.json"), "w") as fh:
        json.dump(res, fh, indent=1, sort_keys=True)
    print(json.dumps({k: v for k, v in res.items()
                      if k in ("ok", "gates_hash_and_provenance", "gates_forbidden_clean",
                               "gates_inventory_exact", "gates_axioms_fail_closed",
                               "findings")}, indent=1))
    return 0 if res["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
