#!/usr/bin/env python3
"""
L4-child-ricci-to-doubling — INDEPENDENT acceptance check (round-3 re-verification).

This is deliberately a *separate* implementation from
`tools/ricci_to_doubling_verify.py`.  It re-checks the acceptance evidence on the frozen
bytes and adds semantic adversarial scans:

  A. hash freeze: the 4 new files and 10 consumed sources match `checkpoint.json`;
  B. axiom cones: parse the *freshly regenerated* `logs/round3-rebuild.log`
     (produced by a forced recompilation with the oleans deleted) and require every cone to
     be a subset of {propext, Classical.choice, Quot.sound}; require 34 declarations;
  C. conclusion-equivalence scan: for each headline model/interface theorem, take the full
     `#check` type text and require that no hypothesis (everything before the final
     conclusion arrow at top level) mentions the conclusion symbols
     (`radialVolume`, `coveringNumber`);
  D. manifold-overclaim scan: no declaration type text may mention Manifold / Riemannian /
     ChartedSpace / TangentBundle / IsManifold, and the two mathematical files may not
     contain the token `Manifold` outside comments/strings in a declaration position;
  E. classification scan: every declaration in the two mathematical files carries exactly one
     `**Class:**` label, and labels are in the approved set;
  F. informal-witness arithmetic: numerically re-verify the snowflake realisation
     (A(t)=4|t|, d(x,y)=sqrt|x-y|, Lebesgue) and the scalar hypotheses
     (m=1/t, dm=-1/t^2, dA=4, d=1, k=0, C=0) that the gap section records informally;
  G. duplication scan: no use of `conjugate_point_bound` / Rauch in the new files;
  H. canonical forbidden-token scan is re-invoked and must report 0 hard matches.

Exit code 0 iff every gate passes.  Writes `evidence/round3-acceptance.json`.
"""
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import datetime

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-ricci-to-doubling"
NEW_FILES = [
    "release/Poincare/L4/Compactness/RicciToDoubling.lean",
    "release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean",
    "release/Audit/RicciToDoublingAudit.lean",
    "release/Audit/RicciToDoublingHyperbolicAudit.lean",
]
MATH_FILES = [
    "release/Poincare/L4/Compactness/RicciToDoubling.lean",
    "release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean",
]
REBUILD_LOG = "logs/round3-rebuild.log"
APPROVED = {"propext", "Classical.choice", "Quot.sound"}
APPROVED_LABELS = {
    "model (scalar ODE)",
    "model (scalar ODE), private helper",
    "metric–measure interface (non-manifold)",
    "metric–measure interface (non-manifold), conditional on the scalar model hypotheses",
}
# (declaration, conclusion head symbol that must not occur in any hypothesis)
HEADLINE = [
    ("euclid_volume_ratio_le_of_ricci_nonneg", "radialVolume"),
    ("euclid_volumeRatio_div_le_of_ricci_nonneg", "radialVolume"),
    ("euclid_volume_doubling_of_ricci_nonneg", "radialVolume"),
    ("hyp_volume_ratio_le_of_ricci_ge", "radialVolume"),
    ("hyp_volume_doubling_of_ricci_ge", "radialVolume"),
    ("hyp_volume_doubling_d1_k1", "radialVolume"),
    ("coveringNumber_le_measure_ratio_of_radialBallMeasure", "coveringNumber"),
    ("coveringNumber_le_of_radialBallMeasure_doubling", "coveringNumber"),
    ("coveringNumber_le_of_ricci_nonneg_radialBallMeasure", "coveringNumber"),
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
        m = re.match(r"^@([\w.]+) : (.*)$", line)
        if m:
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
    """Split a `∀ ..., h1 → h2 → ... → concl` type into (hypotheses, conclusion).

    Operates on the token stream, tracking bracket depth, so arrows inside hypotheses
    (e.g. `∀ t, ... → ...` and function types) are not mistaken for top-level arrows.
    """
    text = " ".join(type_text.split())
    depth = 0
    arrows = []
    i = 0
    while i < len(text):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "→" and depth == 0:
            arrows.append(i)
        i += 1
    if not arrows:
        return [], text
    split = arrows[-1]
    body = text[:split]
    concl = text[split + 1:]
    # drop the binder prefix before the last top-level binder arrow chain
    hyps = [h.strip() for h in re.split(r"→", body) if h.strip()]
    return hyps, concl.strip()


def main():
    res = {"schema": "l4-child-ricci-to-doubling/round3-acceptance-v1",
           "generated_at": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
           "gates": {}, "pass": False}
    failures = []

    def gate(name, ok, detail):
        res["gates"][name] = {"pass": bool(ok), "detail": detail}
        if not ok:
            failures.append(name)

    # A. hash freeze vs checkpoint
    cp = json.load(open(os.path.join(WT, "checkpoint.json")))
    expected = {}
    for a in cp["new_artifacts"]:
        if "sha256" in a:
            expected[a["file"]] = a["sha256"]
    actual = {f: sha256(os.path.join(WT, f)) for f in NEW_FILES}
    hash_ok = all(actual.get(f) == expected.get(f) for f in NEW_FILES)
    gate("hash_freeze_new_files", hash_ok, {"actual": actual, "expected": expected})

    # B. axiom cones from the forced-rebuild log
    log = open(os.path.join(WT, REBUILD_LOG)).read()
    cones = {}
    for line in log.splitlines():
        m = re.match(r"AXIOM-JSON ([\w.]+): (.*)$", line.strip())
        if m:
            cones[m.group(1)] = [a for a in m.group(2).split(",") if a]
    cone_ok = len(cones) == 34 and all(set(ax) <= APPROVED for ax in cones.values())
    bad = {n: ax for n, ax in cones.items() if not set(ax) <= APPROVED}
    gate("axiom_cones_subset_classical_trio",
         cone_ok and "BUILD-EXIT=0" in log and "AUDIT1-EXIT=0" in log and "AUDIT2-EXIT=0" in log,
         {"declarations": len(cones), "violations": bad,
          "forced_rebuild_exit_0": "BUILD-EXIT=0" in log,
          "audit_exits_0": ("AUDIT1-EXIT=0" in log and "AUDIT2-EXIT=0" in log),
          "axiom_pass_lines": [l for l in log.splitlines() if "AXIOM-AUDIT PASS" in l]})

    # C. conclusion-equivalence scan on the fresh #check signatures.
    #    For each headline theorem, require that no top-level hypothesis mentions the
    #    conclusion's head symbol (`radialVolume` for the model theorems, `coveringNumber`
    #    for the interface theorems).  Positivity side conditions such as
    #    `0 < radialVolume A (r/2)` are allowed for interface theorems (they mention the
    #    numerator symbol but not the conclusion head) and are recorded explicitly.
    sigs = split_check_output(log)
    ce_report = {}
    ce_ok = True
    for name, concl_head in HEADLINE:
        if name not in sigs:
            ce_ok = False
            ce_report[name] = "SIGNATURE-MISSING"
            continue
        hyps, concl = top_level_hypotheses(sigs[name])
        leaked = [h for h in hyps if concl_head in h]
        radial_in_hyps = [h for h in hyps if "radialVolume" in h]
        ce_report[name] = {"conclusion_head": concl_head,
                           "conclusion_head_in_conclusion": concl_head in concl,
                           "hypotheses_mentioning_conclusion_head": leaked,
                           "hypotheses_mentioning_radialVolume": radial_in_hyps,
                           "n_top_level_hypotheses": len(hyps)}
        if leaked or concl_head not in concl:
            ce_ok = False
    gate("no_conclusion_equivalent_hypothesis", ce_ok, ce_report)

    # D. manifold-overclaim scan on declaration type texts
    mo_report = {}
    mo_ok = True
    for name, text in sigs.items():
        hits = [t for t in MANIFOLD_TOKENS if t in text]
        if hits:
            mo_report[name] = hits
            mo_ok = False
    # also: stripped source of the two math files must not contain a manifold token in code
    src_hits = {}
    for f in MATH_FILES:
        code = strip_lean_comments_and_strings(open(os.path.join(WT, f)).read())
        hits = [t for t in MANIFOLD_TOKENS if t in code]
        if hits:
            src_hits[f] = hits
            mo_ok = False
    gate("no_manifold_overclaim", mo_ok, {"declaration_type_hits": mo_report,
                                          "source_code_hits": src_hits})

    # E. classification labels: pair each declaration with the docstring immediately
    #    preceding it and require exactly one approved `**Class:**` label.
    label_report, label_ok = {}, True
    pair_re = re.compile(
        r"/--(.*?)-/\s*^[ \t]*((?:private )?(?:noncomputable )?(?:theorem|lemma|def)[ \t]+[\w']+)",
        re.S | re.M)
    for f in MATH_FILES:
        text = open(os.path.join(WT, f)).read()
        decls = re.findall(r"^[ \t]*(?:private )?(?:noncomputable )?(?:theorem|lemma|def)[ \t]+([\w']+)",
                           text, re.M)
        labels, names = [], []
        for m in pair_re.finditer(text):
            doc, declname = m.group(1), m.group(2)
            # a `**Class:**` line may wrap onto continuation lines until a blank line
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
        if len(decls) != len(labels) or bad_labels or len(names) != len(set(names)):
            label_ok = False
    total_decls = sum(v["declarations"] for v in label_report.values())
    gate("classification_labels_36_36", label_ok and total_decls == 36, label_report)

    # F. informal snowflake witness arithmetic (independent numeric re-verification)
    def radial_exact(s):
        return 2.0 * s * abs(s)          # ∫₀ˢ 4|t| dt = 2 s |s|

    def radial_numeric(s, n=200001):
        # Simpson on [0,s] (signed), f(t)=4|t|
        if s == 0:
            return 0.0
        a, b = (0.0, s) if s > 0 else (s, 0.0)
        h = (b - a) / (n - 1)
        tot = 0.0
        for i in range(n):
            t = a + i * h
            w = 1 if i in (0, n - 1) else (4 if i % 2 == 1 else 2)
            tot += w * 4.0 * abs(t)
        val = tot * h / 3.0
        return val if s > 0 else -val

    snow_checks = {}
    snow_ok = True
    for s in (-1.3, -0.5, 0.0, 0.25, 1.0, 2.7):
        num, exact = radial_numeric(s), radial_exact(s)
        ok = abs(num - exact) < 1e-6 * max(1.0, abs(exact))
        snow_checks[f"radialVolume_A4abs({s})"] = {"numeric": num, "exact_2s|s|": exact, "ok": ok}
        snow_ok &= ok
        # closedBall in the snowflake metric has Lebesgue measure 2 s^2 for s >= 0, 0 for s < 0
        mu = 2.0 * s * s if s >= 0 else 0.0
        ofreal = max(exact, 0.0)          # ENNReal.ofReal truncates negatives
        ok2 = abs(mu - ofreal) < 1e-9
        snow_checks[f"ball_measure({s})"] = {"mu_snowflake": mu, "ofReal_radial": ofreal, "ok": ok2}
        snow_ok &= ok2
    # scalar hypotheses on (0,T) with d=1, m=1/t, dm=-1/t^2, A=4t, dA=4, k=0, C=0
    for t in (0.1, 0.7, 3.3, 9.9):
        riccati = -1.0 / t**2 + (1.0 / t) ** 2 / 1.0 + 0.0
        deriv = abs(1.0 / t - 4.0 / (4.0 * t))
        norm = abs(1.0 / t - 1.0 / t) - 0.0
        ok = abs(riccati) < 1e-12 and deriv < 1e-12 and norm <= 0
        snow_checks[f"scalar_hypotheses(t={t})"] = {
            "riccati_value": riccati, "m_minus_dA_over_A": deriv,
            "normalization_slack": norm, "ok": ok}
        snow_ok &= ok
    gate("informal_joint_witness_arithmetic", snow_ok, snow_checks)

    # G. duplication scan
    dup = {}
    for f in MATH_FILES:
        code = strip_lean_comments_and_strings(open(os.path.join(WT, f)).read())
        hits = [t for t in ("conjugate_point_bound", "Rauch", "rauch") if t in code]
        if hits:
            dup[f] = hits
    gate("no_rauch_conjugate_point_duplication", not dup, dup)

    # H. canonical forbidden scanner
    scan = subprocess.run(
        [sys.executable, os.path.join(WT, "input/d5-tools/scan_forbidden.py")]
        + [os.path.join(WT, f) for f in NEW_FILES],
        capture_output=True, text=True)
    gate("canonical_forbidden_scan", scan.returncode == 0,
         {"returncode": scan.returncode, "stdout_tail": scan.stdout[-800:],
          "stderr_tail": scan.stderr[-400:]})

    # I. statement fidelity: the required conclusion forms from the acceptance text must
    #    occur (after canonicalising qualified names / coercions / whitespace) in the
    #    corresponding full signature.
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
    }
    fid_report, fid_ok = {}, True
    for name, needles in fidelity.items():
        text = canon(sigs.get(name, ""))
        missing = [n for n in needles if canon(n) not in text]
        fid_report[name] = {"missing": missing}
        if missing or name not in sigs:
            fid_ok = False
    # the interface predicate body: `#check` on a `def` prints only its type, so the body
    # is checked in the comment/string-stripped source (the compiled discharge theorems
    # unfold it, which the axiom audit exercises).
    iface_src = strip_lean_comments_and_strings(
        open(os.path.join(WT, "release/Poincare/L4/Compactness/RicciToDoubling.lean")).read())
    iface_body = canon("μ (closedBall x s) = ENNReal.ofReal (radialVolume A s)")
    iface_decl = "defIsRadialBallMeasure"
    iface_ok = iface_body in canon(iface_src) and iface_decl in canon(iface_src)
    fid_report["IsRadialBallMeasure"] = {
        "body_present_in_stripped_source": iface_body in canon(iface_src),
        "declaration_present": iface_decl in canon(iface_src),
        "check_type": " ".join(sigs.get("IsRadialBallMeasure", "").split())}
    fid_ok &= iface_ok
    gate("statement_fidelity_to_acceptance_text", fid_ok, fid_report)

    res["pass"] = not failures
    res["failures"] = failures
    res["tool_sha256"] = sha256(os.path.abspath(__file__))
    res["rebuild_log"] = REBUILD_LOG
    res["rebuild_log_sha256"] = sha256(os.path.join(WT, REBUILD_LOG))
    out = os.path.join(WT, "evidence/round3-acceptance.json")
    with open(out, "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)
    print(json.dumps({k: v["pass"] for k, v in res["gates"].items()}, indent=1))
    print("INDEPENDENT-ACCEPTANCE:", "PASS" if res["pass"] else "FAIL", "->", out)
    if failures:
        print("FAILED GATES:", failures)
        for name in failures:
            print("---", name, json.dumps(res["gates"][name]["detail"], indent=1)[:2000])
    return 0 if res["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
