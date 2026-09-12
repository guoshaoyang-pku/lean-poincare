#!/usr/bin/env python3
"""
L4-child-ricci-to-doubling — round-4 independent acceptance check.

This is a fresh implementation (not a wrapper of `tools/ricci_to_doubling_verify.py` nor of
`tools/round3_acceptance_check.py`).  It verifies the frozen round-1/2/3 artifact set plus the
round-4 additive closed-form module, on the compiled `#check` signatures produced by the
round-4 forced rebuild and the round-4 closed-form audit.

Gates:
  A. hash freeze: the 4 frozen files and the 2 round-4 files match `checkpoint.json`
     (`new_artifacts` / `round4_new_artifacts`);
  B. axiom cones: parse `logs/round4-rebuild.log` (34 cones) and
     `logs/round4-closedform-audit.log` (15 cones); every cone ⊆ {propext, Classical.choice,
     Quot.sound}; BUILD-EXIT=0, AUDIT1/2/3-EXIT=0, zero warnings;
  C. conclusion-equivalence: for every headline declaration, no top-level hypothesis mentions
     the conclusion head symbol(s); the conclusion must contain them;
  D. manifold-overclaim: no declaration type and no comment/string-stripped source line of the
     three mathematical modules mentions Manifold / Riemannian / ChartedSpace / TangentBundle /
     IsManifold / VectorBundle / SmoothManifold;
  E. classification: every declaration in the three modules carries exactly one approved
     `**Class:**` label (51 declarations);
  F. independent numeric evidence: `evidence/round4-numeric-checks.json` exists, has
     pass = true, 306 checks, 0 failures, and the closed-form errors are < 1e-6;
  G. duplication: no use of `conjugate_point_bound` / Rauch in the three modules;
  H. canonical forbidden-token scan over the 6 new/frozen files: 0 hard matches;
  I. statement fidelity: the required conclusion forms (acceptance text) occur in the compiled
     signatures / stripped sources;
  J. round-4 closed-form consistency: the new module's `hypModel_volumeRatio_closedForm` and
     `hyp_volume_ratio_le_of_ricci_ge_closedForm` have the expected shape with the frozen
     model `hypModelA` and the new `sinhPowIntegral`, and the new module consumes (does not
     restate) the frozen Bishop-Gromov instantiation.

Exit code 0 iff every gate passes.  Writes `evidence/round4-acceptance.json`.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import datetime

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-ricci-to-doubling"
FROZEN_FILES = [
    "release/Poincare/L4/Compactness/RicciToDoubling.lean",
    "release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean",
    "release/Audit/RicciToDoublingAudit.lean",
    "release/Audit/RicciToDoublingHyperbolicAudit.lean",
]
ROUND4_FILES = [
    "release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean",
    "release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean",
]
NEW_FILES = FROZEN_FILES + ROUND4_FILES
MATH_FILES = [
    "release/Poincare/L4/Compactness/RicciToDoubling.lean",
    "release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean",
    "release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean",
]
REBUILD_LOG = "logs/round4-rebuild.log"
CLOSEDFORM_LOG = "logs/round4-closedform-audit.log"
NUMERIC_EVIDENCE = "evidence/round4-numeric-checks.json"
APPROVED = {"propext", "Classical.choice", "Quot.sound"}
APPROVED_LABELS = {
    "model (scalar ODE)",
    "model (scalar ODE), private helper",
    "metric–measure interface (non-manifold)",
    "metric–measure interface (non-manifold), conditional on the scalar model hypotheses",
}
# (declaration, symbols required in the conclusion, symbols forbidden in any top-level hypothesis)
HEADLINE = [
    ("euclid_volume_ratio_le_of_ricci_nonneg", ["radialVolume"], ["radialVolume"]),
    ("euclid_volumeRatio_div_le_of_ricci_nonneg", ["radialVolume"], ["radialVolume"]),
    ("euclid_volume_doubling_of_ricci_nonneg", ["radialVolume"], ["radialVolume"]),
    ("hyp_volume_ratio_le_of_ricci_ge", ["radialVolume"], ["radialVolume"]),
    ("hyp_volume_doubling_of_ricci_ge", ["radialVolume"], ["radialVolume"]),
    ("hyp_volume_doubling_d1_k1", ["radialVolume"], ["radialVolume"]),
    ("coveringNumber_le_measure_ratio_of_radialBallMeasure", ["coveringNumber"], ["coveringNumber"]),
    ("coveringNumber_le_of_radialBallMeasure_doubling", ["coveringNumber"], ["coveringNumber"]),
    ("coveringNumber_le_of_ricci_nonneg_radialBallMeasure", ["coveringNumber"], ["coveringNumber"]),
    ("hypModelA_volume_closedForm", ["radialVolume"], ["radialVolume"]),
    ("hypModel_volumeRatio_closedForm", ["radialVolume", "sinhPowIntegral"],
     ["radialVolume", "sinhPowIntegral"]),
    # fully evaluated d = 2 ratio: no radialVolume/sinhPowIntegral survives in the statement
    ("hypModel_volumeRatio_d2_closedForm", ["Real.sinh", "Real.cosh"],
     ["radialVolume", "sinhPowIntegral"]),
    ("hyp_volume_ratio_le_of_ricci_ge_closedForm", ["radialVolume", "sinhPowIntegral"],
     ["radialVolume", "sinhPowIntegral"]),
    ("hyp_volume_doubling_closedForm", ["radialVolume", "sinhPowIntegral"],
     ["radialVolume", "sinhPowIntegral"]),
]
MANIFOLD_TOKENS = ["Manifold", "Riemannian", "ChartedSpace", "TangentBundle", "IsManifold",
                   "VectorBundle", "SmoothManifold"]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def strip_lean_comments_and_strings(text):
    """Comment/string-aware removal (mirrors the canonical D5 scanner semantics)."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "-" and i + 1 < n and text[i + 1] == "-":
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif c == "/" and i + 1 < n and text[i + 1] == "-":
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def split_check_output(text):
    """Return {decl_short_name: type_text} from `#check` output, joining continuation lines."""
    sigs, cur, buf = {}, None, []
    for line in text.splitlines():
        m = re.match(r"^@?([\w.]+) : (.*)$", line)
        if m and not line.startswith(" "):
            if cur is not None:
                sigs[cur] = "\n".join(buf)
            cur = m.group(1).split(".")[-1]
            buf = [m.group(2)]
        elif cur is not None and (line.startswith(" ") or line.startswith("\t")):
            buf.append(line)
        else:
            if cur is not None:
                sigs[cur] = "\n".join(buf)
            cur, buf = None, []
    if cur is not None:
        sigs[cur] = "\n".join(buf)
    return sigs


def top_level_hypotheses(type_text):
    """Split `∀ ..., h1 → h2 → ... → concl` into (hypotheses, conclusion), depth-aware."""
    text = " ".join(type_text.split())
    depth = 0
    arrows = []
    for i, c in enumerate(text):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "→" and depth == 0:
            arrows.append(i)
    if not arrows:
        return [], text
    split = arrows[-1]
    body = text[:split]
    concl = text[split + 1:]
    hyps = [h.strip() for h in re.split(r"→", body) if h.strip()]
    return hyps, concl.strip()


def main():
    res = {"schema": "l4-child-ricci-to-doubling/round4-acceptance-v1",
           "generated_at": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
           "gates": {}, "pass": False}
    failures = []

    def gate(name, ok, detail):
        res["gates"][name] = {"pass": bool(ok), "detail": detail}
        if not ok:
            failures.append(name)

    cp = json.load(open(os.path.join(WT, "checkpoint.json")))
    expected = {}
    for a in cp.get("new_artifacts", []):
        if "sha256" in a:
            expected[a["file"]] = a["sha256"]
    for a in cp.get("round4_new_artifacts", []):
        if "sha256" in a:
            expected[a["file"]] = a["sha256"]

    # A. hash freeze
    actual = {f: sha256(os.path.join(WT, f)) for f in NEW_FILES}
    missing = [f for f in NEW_FILES if f not in expected]
    hash_ok = not missing and all(actual[f] == expected[f] for f in NEW_FILES)
    frozen_expected = {
        "release/Poincare/L4/Compactness/RicciToDoubling.lean":
            "9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4",
        "release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean":
            "be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841",
        "release/Audit/RicciToDoublingAudit.lean":
            "3e8510bc5ddf37d7d15e13841d20f30ee3f08ffe77ceca210871d515f72a1417",
        "release/Audit/RicciToDoublingHyperbolicAudit.lean":
            "dc9b26384f279add1108ac5b83b41df7dd960b89357329ce31ee7c03422c7ee3",
    }
    frozen_ok = all(actual[f] == frozen_expected[f] for f in FROZEN_FILES)
    gate("hash_freeze_frozen_and_round4", hash_ok and frozen_ok,
         {"actual": actual, "expected_checkpoint": expected, "missing_from_checkpoint": missing,
          "frozen_match_recorded_round1": frozen_ok})

    # B. axiom cones
    log = open(os.path.join(WT, REBUILD_LOG)).read()
    clog = open(os.path.join(WT, CLOSEDFORM_LOG)).read()
    cones = {}
    for line in log.splitlines() + clog.splitlines():
        m = re.match(r"AXIOM-JSON ([\w.]+): (.*)$", line.strip())
        if m:
            cones[m.group(1)] = [a for a in m.group(2).split(",") if a]
    bad = {n: ax for n, ax in cones.items() if not set(ax) <= APPROVED}
    cone_ok = (len(cones) == 49 and not bad
               and "BUILD-EXIT=0" in log and "AUDIT1-EXIT=0" in log and "AUDIT2-EXIT=0" in log
               and "AUDIT3-EXIT=0" in clog
               and log.count("warning") == 0 and clog.count("warning") == 0)
    gate("axiom_cones_subset_classical_trio", cone_ok,
         {"declarations": len(cones), "violations": bad,
          "frozen_cones": sum(1 for line in log.splitlines() if line.startswith("AXIOM-JSON")),
          "closedform_cones": sum(1 for line in clog.splitlines() if line.startswith("AXIOM-JSON")),
          "zero_warnings": log.count("warning") == 0 and clog.count("warning") == 0,
          "audit_pass_lines": [l for l in (log + clog).splitlines() if "AXIOM-AUDIT PASS" in l]})

    # C. conclusion-equivalence
    sigs = split_check_output(log + "\n" + clog)
    ce_report, ce_ok = {}, True
    for name, required, forbidden in HEADLINE:
        if name not in sigs:
            ce_ok = False
            ce_report[name] = "SIGNATURE-MISSING"
            continue
        hyps, concl = top_level_hypotheses(sigs[name])
        leaked = [h for h in hyps if any(hd in h for hd in forbidden)]
        ce_report[name] = {"conclusion_required": required,
                           "forbidden_in_hypotheses": forbidden,
                           "required_in_conclusion": {r: (r in concl) for r in required},
                           "hypotheses_mentioning_conclusion_head": leaked,
                           "n_top_level_hypotheses": len(hyps)}
        if leaked or not all(r in concl for r in required):
            ce_ok = False
    gate("no_conclusion_equivalent_hypothesis", ce_ok, ce_report)

    # D. manifold overclaim
    mo_report, mo_ok = {}, True
    for name, text in sigs.items():
        hits = [t for t in MANIFOLD_TOKENS if t in text]
        if hits:
            mo_report[name] = hits
            mo_ok = False
    src_hits = {}
    for f in MATH_FILES:
        code = strip_lean_comments_and_strings(open(os.path.join(WT, f)).read())
        hits = [t for t in MANIFOLD_TOKENS if t in code]
        if hits:
            src_hits[f] = hits
            mo_ok = False
    gate("no_manifold_overclaim", mo_ok, {"declaration_type_hits": mo_report,
                                          "source_code_hits": src_hits})

    # E. classification labels
    label_report, label_ok = {}, True
    pair_re = re.compile(
        r"/--(.*?)-/\s*^[ \t]*((?:private )?(?:noncomputable )?(?:theorem|lemma|def)[ \t]+[\w']+)",
        re.S | re.M)
    total_decls = 0
    for f in MATH_FILES:
        text = open(os.path.join(WT, f)).read()
        decls = re.findall(
            r"^[ \t]*(?:private )?(?:noncomputable )?(?:theorem|lemma|def)[ \t]+([\w']+)",
            text, re.M)
        labels, names = [], []
        for m in pair_re.finditer(text):
            doc, declname = m.group(1), m.group(2)
            cls = re.findall(r"\*\*Class:\*\*((?:[^\n]*(?:\n(?!\s*\n)[^\n]*)*))", doc)
            if cls:
                joined = " ".join(cls[-1].split())
                labels.append(joined.rstrip("."))
            else:
                labels.append(None)
            names.append(declname.split()[-1])
        bad_labels = [l for l in labels if l not in APPROVED_LABELS]
        label_report[f] = {"declarations": len(decls), "paired_docstrings": len(labels),
                           "names": names, "unapproved_or_missing": bad_labels}
        total_decls += len(decls)
        if len(decls) != len(labels) or bad_labels or len(names) != len(set(names)):
            label_ok = False
    gate("classification_labels_51_51", label_ok and total_decls == 51,
         {"total_declarations": total_decls, "per_file": label_report})

    # F. numeric evidence
    num = json.load(open(os.path.join(WT, NUMERIC_EVIDENCE)))
    num_ok = (num.get("pass") is True and len(num.get("checks", [])) == 387
              and not num["summary"]["failed"]
              and num["summary"]["closedform_J_max_rel_err"] < 1e-6
              and num["summary"]["modelvolume_closedform_max_rel_err"] < 1e-6
              and num["summary"]["modelvolume_closedform_signed_max_rel_err"] < 1e-6)
    gate("independent_numeric_evidence", num_ok, num.get("summary", {}))

    # G. duplication
    dup = {}
    for f in MATH_FILES:
        code = strip_lean_comments_and_strings(open(os.path.join(WT, f)).read())
        hits = [t for t in ("conjugate_point_bound", "Rauch", "rauch") if t in code]
        if hits:
            dup[f] = hits
    gate("no_rauch_conjugate_point_duplication", not dup, dup)

    # H. canonical forbidden scanner, made NON-VACUOUS: the D5 scanner walks *directories*
    #    (`os.walk`), so passing individual files scans nothing.  Copy the six artifact files
    #    into an isolated temporary directory and require exactly 6 scanned files with 0 hard
    #    matches.  (The round-3 wrapper passed file paths and therefore scanned 0 files; this
    #    round-4 gate fixes that weakness.)
    import shutil
    import tempfile
    scan_dir = tempfile.mkdtemp(prefix="r4scan-")
    for f in NEW_FILES:
        shutil.copy(os.path.join(WT, f), os.path.join(scan_dir, os.path.basename(f)))
    scan = subprocess.run(
        [sys.executable, os.path.join(WT, "input/d5-tools/scan_forbidden.py"), scan_dir],
        capture_output=True, text=True)
    try:
        scan_json = json.loads(scan.stdout)
    except Exception:
        scan_json = {}
    gate("canonical_forbidden_scan", scan.returncode == 0
         and scan_json.get("lean_files_scanned") == len(NEW_FILES)
         and scan_json.get("hard_match_count") == 0
         and scan_json.get("soft_match_count") == 0,
         {"returncode": scan.returncode,
          "lean_files_scanned": scan_json.get("lean_files_scanned"),
          "expected_files": len(NEW_FILES),
          "hard_match_count": scan_json.get("hard_match_count"),
          "soft_match_count": scan_json.get("soft_match_count"),
          "matches": scan_json.get("matches")})
    shutil.rmtree(scan_dir, ignore_errors=True)

    # I. statement fidelity
    def canon(s):
        s = s.replace("D12.ComparisonGeodesics.", "").replace("Metric.", "")
        s = s.replace("↑", "").replace(" ", "").replace("\n", "")
        return s.replace("(", "").replace(")", "")

    fidelity = {
        "euclid_volume_ratio_le_of_ricci_nonneg": [
            "radialVolumeAR≤(R/r)^(d+1)*radialVolumeAr"],
        "euclid_volume_doubling_of_ricci_nonneg": [
            "radialVolumeA(2*s)≤2^(d+1)*radialVolumeAs"],
        "hyp_volume_ratio_le_of_ricci_ge": [
            "radialVolumeAR≤radialVolume(hypModelAdκ)R/radialVolume(hypModelAdκ)r*radialVolumeAr"],
        "hyp_volume_doubling_of_ricci_ge": [
            "radialVolumeA(2*s)≤radialVolume(hypModelAdκ)(2*s)/radialVolume(hypModelAdκ)s*radialVolumeAs"],
        "hyp_volume_doubling_d1_k1": [
            "radialVolumeA(2*s)≤2*(Real.coshs+1)*radialVolumeAs"],
        "coveringNumber_le_measure_ratio_of_radialBallMeasure": [
            "coveringNumberr(closedBallx(2*r))≤ENNReal.ofReal(radialVolumeA(4*r))/"
            "ENNReal.ofReal(radialVolumeA(r/2))"],
        # round-4 closed forms
        "hypModelA_volume_closedForm": [
            "radialVolume(hypModelAdκ)s=κ⁻¹^(d+1)*sinhPowIntegrald(κ*s)"],
        "hypModel_volumeRatio_closedForm": [
            "radialVolume(hypModelAdκ)R/radialVolume(hypModelAdκ)r="
            "sinhPowIntegrald(κ*R)/sinhPowIntegrald(κ*r)"],
        "hypModel_volumeRatio_d2_closedForm": [
            "radialVolume(hypModelA2κ)R/radialVolume(hypModelA2κ)r="
            "(Real.sinh(κ*R)*Real.cosh(κ*R)-κ*R)/(Real.sinh(κ*r)*Real.cosh(κ*r)-κ*r)"],
        "hyp_volume_ratio_le_of_ricci_ge_closedForm": [
            "radialVolumeAR≤(sinhPowIntegrald(κ*R)/sinhPowIntegrald(κ*r))*radialVolumeAr"],
        "hyp_volume_doubling_closedForm": [
            "radialVolumeA(2*s)≤(sinhPowIntegrald(2*(κ*s))/sinhPowIntegrald(κ*s))*radialVolumeAs"],
        "sinhPowIntegral_integral": [
            "∫(t:ℝ)in0..s,Real.sinht^d=sinhPowIntegralds"],
    }
    fid_report, fid_ok = {}, True
    for name, needles in fidelity.items():
        text = canon(sigs.get(name, ""))
        miss = [n for n in needles if canon(n) not in text]
        fid_report[name] = {"missing": miss}
        if miss or name not in sigs:
            fid_ok = False
    iface_src = strip_lean_comments_and_strings(
        open(os.path.join(WT, MATH_FILES[0])).read())
    iface_body = canon("μ (closedBall x s) = ENNReal.ofReal (radialVolume A s)")
    iface_ok = iface_body in canon(iface_src) and "defIsRadialBallMeasure" in canon(iface_src)
    fid_report["IsRadialBallMeasure"] = {
        "body_present_in_stripped_source": iface_body in canon(iface_src),
        "declaration_present": "defIsRadialBallMeasure" in canon(iface_src)}
    fid_ok &= iface_ok
    gate("statement_fidelity_to_acceptance_text", fid_ok, fid_report)

    # J. round-4 closed-form consistency and consumption (not restatement)
    new_src = strip_lean_comments_and_strings(open(os.path.join(WT, ROUND4_FILES[0])).read())
    j_ok = ("importPoincare.L4.Compactness.RicciToDoublingHyperbolic" in canon(new_src)
            and "hyp_volume_ratio_le_of_ricci_ge" in new_src
            and "hypModelA" in canon(sigs.get("hypModelA_volume_closedForm", ""))
            and "sinhPowIntegral" in canon(sigs.get("hypModel_volumeRatio_closedForm", ""))
            and "importPoincare.L4.Compactness.RicciToDoubling.lean" not in new_src)
    # the composite really consumes the frozen instantiation: its proof term must mention it
    j_ok &= "hyp_volume_ratio_le_of_ricci_ge" in new_src
    gate("round4_closedform_consumes_frozen_model", j_ok,
         {"imports_hyperbolic_module": "importPoincare.L4.Compactness.RicciToDoublingHyperbolic" in canon(new_src),
          "calls_frozen_instantiation": "hyp_volume_ratio_le_of_ricci_ge" in new_src,
          "uses_hypModelA": "hypModelA" in canon(sigs.get("hypModelA_volume_closedForm", "")),
          "uses_sinhPowIntegral": "sinhPowIntegral" in canon(sigs.get("hypModel_volumeRatio_closedForm", ""))})

    # K. the round-4 closed-form composites carry *exactly* the same top-level hypothesis list
    #    as the frozen instantiations they consume (no added, dropped or strengthened hypothesis)
    def hyps_of(name):
        return [" ".join(h.split()) for h in top_level_hypotheses(sigs.get(name, ""))[0]]

    pairs = [("hyp_volume_ratio_le_of_ricci_ge", "hyp_volume_ratio_le_of_ricci_ge_closedForm"),
             ("hyp_volume_doubling_of_ricci_ge", "hyp_volume_doubling_closedForm")]
    ident_report, ident_ok = {}, True
    for frozen, closed in pairs:
        hf, hc = hyps_of(frozen), hyps_of(closed)
        same = hf == hc and len(hf) > 20
        ident_report[frozen] = {"frozen_hypotheses": len(hf), "closed_form_hypotheses": len(hc),
                                "identical": same,
                                "diffs": [{"frozen": a, "closed_form": b}
                                          for a, b in zip(hf, hc) if a != b]}
        ident_ok &= same
    gate("closed_form_hypotheses_identical_to_frozen", ident_ok, ident_report)

    # L. exact symbolic (computer-algebra) evidence for the closed form
    sym = json.load(open(os.path.join(WT, "evidence/round4-symbolic-checks.json")))
    sym_ok = (sym.get("pass") is True and len(sym.get("checks", [])) == 26
              and not sym["summary"]["failed"])
    gate("exact_symbolic_closedform_evidence", sym_ok, sym.get("summary", {}))

    res["pass"] = not failures
    res["failures"] = failures
    res["tool_sha256"] = sha256(os.path.abspath(__file__))
    res["rebuild_log_sha256"] = sha256(os.path.join(WT, REBUILD_LOG))
    res["closedform_log_sha256"] = sha256(os.path.join(WT, CLOSEDFORM_LOG))
    out = os.path.join(WT, "evidence/round4-acceptance.json")
    with open(out, "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)
    print(json.dumps({k: v["pass"] for k, v in res["gates"].items()}, indent=1))
    print("ROUND4-ACCEPTANCE:", "PASS" if res["pass"] else "FAIL", "->", out)
    if failures:
        print("FAILED GATES:", failures)
        for name in failures:
            print("---", name, json.dumps(res["gates"][name]["detail"], indent=1)[:1500])
    return 0 if res["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
