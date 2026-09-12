#!/usr/bin/env python3
"""
Pass-6 independent acceptance check for `L4-child-sturm-zero-interlacing`.

Continuation invocation (2026-09-12).  This driver is independent of
`tools/run_sturm_gates.py`, `tools/acceptance_pass2.py`, `tools/acceptance_pass3.py`,
`tools/gs_independent_check.py` and `tools/acceptance_pass5.py`.  It uses its own fresh probe
`tmp/acceptance_probe_r6.lean` and re-derives the release-level facts from the files on disk.

What pass 6 adds beyond passes 1-5:

  A. **Gate sensitivity (mutation) testing.**  The earlier passes established that the
     fail-closed gates *accept* the pristine artifact.  Pass 6 establishes that they *reject*
     deliberately poisoned artifacts, using the gate driver's own parser and allow-list:
       - `tmp/mutation/poisoned_audit.lean` introduces a new axiom and a theorem depending on
         it; the audit must report an out-of-cone violation;
       - `tmp/mutation/truncated_audit.lean` omits most declarations of the real audit
         module; the coverage check (every declaration of the two deliverable modules must be
         reported) must fire — this is the layer that catches truncation, since the naive
         expected-vs-reported check cannot;
       - `tmp/mutation/scan_targets/real_sorry.lean` contains a real `sorry` and must be
         flagged, while `tmp/mutation/scan_targets/comment_only.lean` contains the same
         tokens only in comments/strings and must not be flagged (false-positive control).
  B. **Statement-level non-restatement checks.**  The `#check @...` surface of the probe is
     parsed: the delivered strict-gap theorem's type must differ from the raw D12 engine's
     disjunctive type and must not contain the `∨`; the delivered closed-interval
     zero-counting theorem must differ from the prior-art strict-excess theorem (`Ioc` versus
     `Ioo`, fewer hypotheses); the engine-derived positivity bound must carry strictly fewer
     hypotheses than the leader's `conjugate_point_bound`.
  C. **Machine-checked non-restatement witness** (in the probe itself): the raw engine is
     invoked on the acceptance data, its two-sided alternative `A ∨ B` is obtained, `¬B` is
     proved, and the delivered theorem supplies `A`.

Standard fail-closed gates re-run here: full project-closure rebuild, fresh probe compile,
per-declaration axiom cones, probe source hygiene, audit-module re-run on the rebuilt
oleans, audit coverage, deliverable hashes against checkpoint cp22, read-only input
byte-identity, shared-file preservation, card verdict, checkpoint integrity.

Outputs `evidence/acceptance-pass6.json`; exits nonzero on any failure.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RELEASE = os.path.join(ROOT, "release")
LEADER = os.path.normpath(os.path.join(ROOT, os.pardir, "leaders",
                                      "L4-geometric-critical-path", "release"))
EV = os.path.join(ROOT, "evidence")
LOGS = os.path.join(ROOT, "logs")
ELAN = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=f"{ELAN}/bin:" + os.environ["PATH"])

sys.path.insert(0, os.path.join(ROOT, "tools"))
import run_sturm_gates as gates  # the gate driver's own parser and allow-list

ALLOWED = set(gates.ALLOWED_AXIOMS)
PROBE = "tmp/acceptance_probe_r6.lean"
PROBE_LOG = "80_pass6_probe.log"
AUDIT_LOG = "81_pass6_audit.log"
CLOSURE_LOG = "82_pass6_closure_rebuild.log"
MUT_POISON_LOG = "83_pass6_mutation_poisoned.log"
MUT_TRUNC_LOG = "84_pass6_mutation_truncated.log"
MUT_SCAN_LOG = "85_pass6_mutation_scan.log"
REL_SCAN_LOG = "86_pass6_release_scan.log"

CORE = "release/Poincare/L4/GeodesicComparison/SturmInterlacing.lean"
CROSS = "release/Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean"
AUDIT = "release/Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean"
AUDIT_REL = "Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean"
NEG = "negcontrol/SturmInterlacingNegativeControl.lean"
CARD_MD = "longrun/results/L4-child-sturm-zero-interlacing.md"
CARD_JSON = "longrun/results/L4-child-sturm-zero-interlacing.json"

MODULES = ["Poincare.L4.GeodesicComparison.SturmInterlacing",
           "Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck",
           "Poincare.L4.GeodesicComparison.SturmInterlacingAxiomAudit"]

CHECKPOINT_CORE = {CORE: None, CROSS: None, AUDIT: None, NEG: None}

MUT_POISON = "tmp/mutation/poisoned_audit.lean"
MUT_TRUNC = "tmp/mutation/truncated_audit.lean"
MUT_SCAN_DIR = "tmp/mutation/scan_targets"

BUILD_ROOT = os.path.join(RELEASE, ".lake", "build", "lib", "lean", "Poincare")

INPUT_FILES = [
    "Poincare/D10/JacobiConstantCurvature/Basic.lean",
    "Poincare/D10/JacobiConstantCurvature/ODE.lean",
    "Poincare/D10/JacobiConstantCurvature/Comparison.lean",
    "Poincare/D12/ComparisonGeodesics/Definitions.lean",
    "Poincare/D12/ComparisonGeodesics/SturmComparison.lean",
    "Poincare/D12/ComparisonGeodesics/SingularRiccati.lean",
    "Poincare/D12/ComparisonGeodesics/VolumeRatio.lean",
    "Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean",
    "Poincare/L4/GeodesicComparison/RauchBridge.lean",
    "Poincare/L4/GeodesicComparison/DownstreamComparison.lean",
    "Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean",
    "Poincare/L4/GeodesicComparison/ConjugatePointBound.lean",
    "Poincare/L4/GeodesicComparison/SturmZeroCount.lean",
]

DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable def|def|abbrev|instance|structure|class)\s+"
    r"([A-Za-z0-9_'.]+)", re.M)

# #check surface the type-level checks rely on
CHECKS = {
    "delivered_gap": "@Poincare.L4.GeodesicComparison.exists_zero_of_curvature_lt",
    "engine_gap": "@Poincare.D12.ComparisonGeodesics.sturm_zero_comparison",
    "delivered_firstzero": "@Poincare.L4.GeodesicComparison.firstPositiveZero_le_pi_sqrt",
    "delivered_zerocount": "@Poincare.L4.GeodesicComparison.exists_jacobi_zero_on_Ioc_pi_sqrt",
    "prior_zerocount": "@Poincare.L4.GeodesicComparison.exists_jacobi_zero_before_pi_sqrt",
    "delivered_bound": "@Poincare.L4.GeodesicComparison.no_positive_solution_past_pi_sqrt",
    "leader_bound": "@Poincare.L4.GeodesicComparison.conjugate_point_bound",
    "delivered_wronskian": "@Poincare.L4.GeodesicComparison.wronskian_sin_linear_antitoneOn",
    "engine_wronskian": "@Poincare.D12.ComparisonGeodesics.wronskian_antitoneOn_of_le",
}

checks = []


def check(name, ok, detail=""):
    checks.append({"check": name, "ok": bool(ok), "detail": detail})
    print(f"[{'OK ' if ok else 'FAIL'}] {name} — {detail}")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_cones(text):
    return gates.parse_axiom_output(text)


def parse_checks(text):
    """Parse the `#check @name : type` blocks of a Lean elaboration transcript.

    Lean prints `@name : type` when there are implicit binders to expose and `name : type`
    otherwise, so both spellings are accepted; keys are normalised by dropping the `@`.
    """
    out, cur, buf = {}, None, []
    for line in text.splitlines():
        if (line[:1] not in (" ", "\t") and " : " in line
                and not line.startswith("'") and line.split(" : ", 1)[0].strip()):
            if cur is not None:
                out[cur] = re.sub(r"\s+", " ", " ".join(buf)).strip()
            cur = line.split(" : ", 1)[0].strip().lstrip("@")
            buf = [line.split(" : ", 1)[1]]
        elif cur is not None:
            buf.append(line)
    if cur is not None:
        out[cur] = re.sub(r"\s+", " ", " ".join(buf)).strip()
    return out


def arrows(t):
    return t.count("→")


def lean_tree_hashes():
    out = {}
    for dirpath, dirnames, filenames in os.walk(RELEASE):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                out[os.path.relpath(p, ROOT)] = sha(p)
    return out


def run_logged(cmd, log_name, cwd=None, timeout=3600):
    log_path = os.path.join(LOGS, log_name)
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {' '.join(cmd)}\n# cwd: {cwd or RELEASE}\n\n")
        log.flush()
        p = subprocess.run(cmd, cwd=cwd or RELEASE, stdout=log, stderr=subprocess.STDOUT,
                           env=ENV, timeout=timeout)
    return (p.returncode, open(log_path).read(), round(time.time() - t0, 2),
            os.path.relpath(log_path, ROOT))


def run_scanner(target, log_name):
    """Run the D5 forbidden-token scanner; returns (exit, parsed_json, log_rel)."""
    log_path = os.path.join(LOGS, log_name)
    cmd = ["python3", os.path.join("input", "d5-tools", "scan_forbidden.py"), target]
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {' '.join(cmd)}\n# cwd: {ROOT}\n\n")
        log.flush()
        p = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                           env=ENV, timeout=600)
    out = open(log_path).read()
    try:
        parsed = json.loads(out[out.index("{"):])
    except Exception:
        parsed = None
    return p.returncode, parsed, os.path.relpath(log_path, ROOT), round(time.time() - t0, 2)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--.*", " ", text)
    return text


def main():
    started = datetime.now(timezone.utc).isoformat()
    cp = json.load(open(os.path.join(ROOT, "checkpoint.json")))
    cp1_at = cp["checkpoints"][0]["at"]
    latest = cp["checkpoints"][-1]
    cp_hashes = latest.get("deliverable_hashes", {})
    cp_id = latest["id"]

    # ---- 1. full project-closure rebuild --------------------------------
    src_before = lean_tree_hashes()
    oleans_deleted = 0
    if os.path.isdir(BUILD_ROOT):
        for dirpath, _dirnames, filenames in os.walk(BUILD_ROOT):
            oleans_deleted += sum(1 for fn in filenames
                                  if fn.endswith((".olean", ".ilean", ".trace")))
        shutil.rmtree(BUILD_ROOT)
    clo_exit, clo_out, clo_secs, clo_log = run_logged(["lake", "build"] + MODULES, CLOSURE_LOG)
    m = re.search(r"Build completed successfully \((\d+) jobs\)", clo_out)
    jobs = int(m.group(1)) if m else -1
    src_after = lean_tree_hashes()
    differing = [k for k in src_before if src_before.get(k) != src_after.get(k)]
    check("closure_rebuild_exit0_jobs", clo_exit == 0 and jobs > 0,
          f"exit={clo_exit} jobs={jobs} oleans_deleted={oleans_deleted} "
          f"seconds={clo_secs} log={clo_log}")
    check("closure_rebuild_left_sources_unchanged", not differing,
          f"lean_files={len(src_before)} differing={differing[:3]}")

    # ---- 2. compile the fresh pass-6 probe ------------------------------
    probe_path = os.path.join(ROOT, PROBE)
    probe_exit, probe_out, probe_secs, probe_log = run_logged(
        ["lake", "env", "lean", os.path.join("..", PROBE)], PROBE_LOG, timeout=1800)
    check("probe_compiles_clean", probe_exit == 0 and "error" not in probe_out,
          f"exit={probe_exit}, seconds={probe_secs}, log={probe_log}")

    # ---- 3. probe axiom cones, fail-closed ------------------------------
    probe_src = open(probe_path).read()
    expected = re.findall(r"#print axioms (\S+)", probe_src)
    cones = parse_cones(probe_out)
    missing = [d for d in expected if d not in cones]
    bad = {d: c for d, c in cones.items() if not set(c) <= ALLOWED}
    sorry = {d: c for d, c in cones.items() if "sorryAx" in c}
    check("probe_axiom_cones_reported_once",
          len(cones) == len(expected) and not missing,
          f"expected={len(expected)} reported={len(cones)} missing={missing}")
    check("probe_axiom_cones_in_allowed_set", not bad and not sorry,
          f"allowed={sorted(ALLOWED)} out_of_cone={bad} sorryAx={sorted(sorry)}")

    # ---- 4. probe source hygiene ---------------------------------------
    tokens = sorted(set(re.findall(
        r"\b(sorry|admit|axiom|unsafe|opaque|partial|native_decide)\b", probe_src)))
    check("probe_source_no_forbidden_tokens", not tokens, f"tokens={tokens}")

    # ---- 5. statement-level type checks ---------------------------------
    types = parse_checks(probe_out)
    ty = {k: types.get(v.lstrip("@"), "") for k, v in CHECKS.items()}
    have_all = all(ty.values())
    check("probe_check_surface_parsed", have_all,
          f"expected={len(CHECKS)} parsed={sum(1 for v in ty.values() if v)} "
          f"missing={[k for k, v in ty.items() if not v]}")

    gap_ok = (bool(ty["delivered_gap"]) and bool(ty["engine_gap"])
              and ty["delivered_gap"] != ty["engine_gap"]
              and "∨" not in ty["delivered_gap"] and "∨" in ty["engine_gap"])
    check("type_nonrestatement_strict_gap", gap_ok,
          f"delivered_has_or={'∨' in ty['delivered_gap']} "
          f"engine_has_or={'∨' in ty['engine_gap']} "
          f"types_equal={ty['delivered_gap'] == ty['engine_gap']} "
          f"delivered_arrows={arrows(ty['delivered_gap'])} "
          f"engine_arrows={arrows(ty['engine_gap'])}")

    zc_ok = (bool(ty["delivered_zerocount"]) and bool(ty["prior_zerocount"])
             and ty["delivered_zerocount"] != ty["prior_zerocount"]
             and "Ioc" in ty["delivered_zerocount"] and "Ioo" in ty["prior_zerocount"]
             and arrows(ty["delivered_zerocount"]) < arrows(ty["prior_zerocount"]))
    check("type_nonduplication_zero_counting", zc_ok,
          f"delivered_arrows={arrows(ty['delivered_zerocount'])} "
          f"prior_arrows={arrows(ty['prior_zerocount'])} "
          f"delivered_Ioc={'Ioc' in ty['delivered_zerocount']} "
          f"prior_Ioo={'Ioo' in ty['prior_zerocount']} "
          f"types_equal={ty['delivered_zerocount'] == ty['prior_zerocount']}")

    wr_ok = (bool(ty["delivered_wronskian"]) and bool(ty["engine_wronskian"])
             and ty["delivered_wronskian"] != ty["engine_wronskian"]
             and "AntitoneOn" in ty["delivered_wronskian"]
             and "AntitoneOn" in ty["engine_wronskian"]
             and arrows(ty["delivered_wronskian"]) < arrows(ty["engine_wronskian"]))
    check("type_engine_instantiated_wronskian", wr_ok,
          f"types_equal={ty['delivered_wronskian'] == ty['engine_wronskian']} "
          f"delivered_arrows={arrows(ty['delivered_wronskian'])} "
          f"engine_arrows={arrows(ty['engine_wronskian'])}")

    lb_ok = (bool(ty["delivered_bound"]) and bool(ty["leader_bound"])
             and ty["delivered_bound"] != ty["leader_bound"]
             and arrows(ty["delivered_bound"]) < arrows(ty["leader_bound"])
             and not re.search(r"\bB\b", ty["delivered_bound"])
             and "t₀" not in ty["delivered_bound"])
    check("type_hypotheses_weaker_than_leader", lb_ok,
          f"delivered_arrows={arrows(ty['delivered_bound'])} "
          f"leader_arrows={arrows(ty['leader_bound'])} "
          f"leader_only_B={'B' in ty['leader_bound']} "
          f"leader_only_t0={'t₀' in ty['leader_bound']}")

    # ---- 6. axiom-audit module re-run on the rebuilt oleans -------------
    ax_exit, ax_out, ax_secs, ax_log = run_logged(
        ["lake", "env", "lean", AUDIT_REL], AUDIT_LOG, timeout=1800)
    ax_expected = re.findall(r"#print axioms (\S+)", open(os.path.join(ROOT, AUDIT)).read())
    ax_cones = parse_cones(ax_out)
    ax_missing = [d for d in ax_expected if d not in ax_cones]
    ax_bad = {d: c for d, c in ax_cones.items() if not set(c) <= ALLOWED}
    ax_sorry = [d for d, c in ax_cones.items() if "sorryAx" in c]
    check("audit_rerun_all_in_cone",
          ax_exit == 0 and not ax_missing and not ax_bad and not ax_sorry
          and len(ax_cones) == len(ax_expected),
          f"exit={ax_exit} expected={len(ax_expected)} reported={len(ax_cones)} "
          f"missing={ax_missing} out_of_cone={ax_bad} sorryAx={ax_sorry} "
          f"seconds={ax_secs} log={ax_log}")

    own = set()
    for rel in (CORE, CROSS):
        own |= set(DECL_RE.findall(open(os.path.join(ROOT, rel)).read()))
    audited = {k.split(".")[-1] for k in ax_cones}
    uncovered = sorted(n for n in own if n not in audited)
    check("audit_covers_every_own_declaration", not uncovered,
          f"own={len(own)} audited_own={len(own & audited)} uncovered={uncovered[:5]}")

    # ---- 7. deliverable hashes against the checkpoint -------------------
    mism = []
    for rel in CHECKPOINT_CORE:
        p = os.path.join(ROOT, rel)
        if not os.path.exists(p) or sha(p) != cp_hashes.get(rel):
            mism.append(rel)
    check(f"deliverable_hashes_match_checkpoint_{cp_id}", not mism,
          f"checkpoint={cp_id} checked={len(CHECKPOINT_CORE)} mismatched={mism}")

    # ---- 8. read-only inputs byte-identical to the leader release -------
    ih_mism = []
    for rel in INPUT_FILES:
        a, b = os.path.join(RELEASE, rel), os.path.join(LEADER, rel)
        if not (os.path.exists(a) and os.path.exists(b) and sha(a) == sha(b)):
            ih_mism.append(rel)
    check("inputs_byte_identical_to_leader", not ih_mism,
          f"files={len(INPUT_FILES)} mismatched={ih_mism}")

    # ---- 9. released tree still clean under the scanner -----------------
    rel_scan_exit, rel_scan, rel_log, rel_secs = run_scanner("release", REL_SCAN_LOG)
    check("release_forbidden_scan_still_clean",
          rel_scan is not None and rel_scan.get("hard_match_count") == 0
          and rel_scan.get("soft_match_count") == 0,
          f"exit={rel_scan_exit} hard={rel_scan and rel_scan.get('hard_match_count')} "
          f"soft={rel_scan and rel_scan.get('soft_match_count')} "
          f"files={rel_scan and rel_scan.get('lean_files_scanned')} log={rel_log}")

    # ---- 10. MUTATION A: audit rejects a poisoned artifact --------------
    mut_a_exit, mut_a_out, mut_a_secs, mut_a_log = run_logged(
        ["lake", "env", "lean", os.path.join("..", MUT_POISON)], MUT_POISON_LOG,
        timeout=1800)
    mut_a_cones = parse_cones(mut_a_out)
    mut_a_viol = [{"declaration": d, "cone": c,
                   "disallowed": [a for a in c if a not in ALLOWED]}
                  for d, c in mut_a_cones.items() if not set(c) <= ALLOWED]
    poison_cone = mut_a_cones.get(
        "Poincare.L4.GeodesicComparison.p6_mutation_poisoned", [])
    pristine_ok = mut_a_cones.get(
        "Poincare.L4.GeodesicComparison.modelJacobiSolutionOn", None)
    mut_a_ok = (mut_a_exit == 0
                and any("p6_mutation_axiom" in a for a in poison_cone)
                and mut_a_viol and pristine_ok is not None and set(pristine_ok) <= ALLOWED)
    check("mutation_axiom_audit_rejects_new_axiom", mut_a_ok,
          f"exit={mut_a_exit} poison_cone={poison_cone} violations={len(mut_a_viol)} "
          f"pristine_cone={pristine_ok} log={mut_a_log}")

    # ---- 11. MUTATION B: coverage detector rejects truncation -----------
    mut_b_exit, mut_b_out, mut_b_secs, mut_b_log = run_logged(
        ["lake", "env", "lean", os.path.join("..", MUT_TRUNC)], MUT_TRUNC_LOG,
        timeout=1800)
    mut_b_cones = parse_cones(mut_b_out)
    mut_b_src_expected = re.findall(
        r"#print axioms (\S+)", open(os.path.join(ROOT, MUT_TRUNC)).read())
    naive_missing = [d for d in mut_b_src_expected if d not in mut_b_cones]
    mut_b_audited = {k.split(".")[-1] for k in mut_b_cones}
    mut_b_uncovered = sorted(n for n in own if n not in mut_b_audited)
    naive_would_pass = (len(mut_b_cones) == len(mut_b_src_expected) and not naive_missing)
    mut_b_ok = mut_b_exit == 0 and bool(mut_b_uncovered)
    check("mutation_coverage_detector_rejects_truncation", mut_b_ok,
          f"exit={mut_b_exit} reported={len(mut_b_cones)} "
          f"source_expected={len(mut_b_src_expected)} naive_would_pass={naive_would_pass} "
          f"uncovered_own_declarations={len(mut_b_uncovered)} "
          f"examples={mut_b_uncovered[:4]} log={mut_b_log}")

    # ---- 12. MUTATION C: scanner sensitivity and false-positive control -
    scan_exit, scan, scan_log, scan_secs = run_scanner(MUT_SCAN_DIR, MUT_SCAN_LOG)
    hard_files = sorted({m["file"] for m in (scan or {}).get("matches", []) if m["hard"]})
    soft_files = sorted({m["file"] for m in (scan or {}).get("matches", []) if not m["hard"]})
    check("mutation_forbidden_scan_rejects_sorry_not_comments",
          scan is not None and scan.get("hard_match_count", 0) >= 1
          and "real_sorry.lean" in hard_files and "comment_only.lean" not in hard_files
          and not soft_files,
          f"exit={scan_exit} hard={scan and scan.get('hard_match_count')} "
          f"hard_files={hard_files} soft_files={soft_files} log={scan_log}")

    # ---- 13. card verdict and checkpoint integrity ----------------------
    card = json.load(open(os.path.join(ROOT, CARD_JSON)))
    md = open(os.path.join(ROOT, CARD_MD)).read()
    card_ok = (card.get("verdict") == "TASK_DONE" and md.rstrip().endswith("**TASK_DONE**"))
    check("card_verdict_task_done", card_ok,
          f"json_verdict={card.get('verdict')} md_ends_task_done="
          f"{md.rstrip().endswith('**TASK_DONE**')}")
    ids = [c["id"] for c in cp["checkpoints"]]
    cps_ok = (len(ids) >= 22 and len(set(ids)) == len(ids)
              and cp["checkpoints"][-1].get("gates") == "PASS"
              and cp.get("current", {}).get("latest") == ids[-1])
    check("checkpoint_history_intact_latest_gates_pass", cps_ok,
          f"entries={len(ids)} unique={len(set(ids))} latest={ids[-1]} "
          f"gates={cp['checkpoints'][-1].get('gates')}")

    # ---- 14. inherited shared files preserved ---------------------------
    own_outputs = {"longrun/results/L4-child-sturm-zero-interlacing.md",
                   "longrun/results/L4-child-sturm-zero-interlacing.json"}
    inherited = []
    for sub in ("manifest", "input", "longrun", "docs", "third_party"):
        base = os.path.join(ROOT, sub)
        if not os.path.isdir(base):
            continue
        for dirpath, _dirnames, filenames in os.walk(base):
            for fn in filenames:
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, ROOT)
                if rel in own_outputs:
                    continue
                inherited.append((rel, os.path.getmtime(p)))
    touched = [r for r, t in inherited
               if datetime.fromtimestamp(t, timezone.utc).isoformat() > cp1_at]
    check("inherited_files_not_modified_during_task", not touched,
          f"files={len(inherited)} modified_since_cp1={touched[:5]}")

    verdict = "PASS" if all(c["ok"] for c in checks) else "FAIL"
    report = {
        "schema": "l4-child-sturm-zero-interlacing/acceptance-pass6-v1",
        "task_id": "L4-child-sturm-zero-interlacing",
        "generated": datetime.now(timezone.utc).isoformat(),
        "started": started,
        "verdict": verdict,
        "probe": {
            "file": PROBE,
            "sha256": sha(probe_path),
            "command": f"lake env lean ../{PROBE} (cwd release/)",
            "compile_exit": probe_exit,
            "seconds": probe_secs,
            "log": probe_log,
            "declarations_audited": len(cones),
            "out_of_cone": bad,
            "theorems": [{"name": k, "cone": v} for k, v in cones.items()],
        },
        "type_checks": {
            "parsed": {k: v for k, v in ty.items() if v},
            "arrow_counts": {k: arrows(v) for k, v in ty.items() if v},
        },
        "closure_rebuild": {
            "command": "lake build " + " ".join(MODULES),
            "exit_code": clo_exit,
            "jobs": jobs,
            "oleans_deleted": oleans_deleted,
            "seconds": clo_secs,
            "log": clo_log,
        },
        "audit_rerun": {
            "command": f"lake env lean {AUDIT_REL} (cwd release/)",
            "exit_code": ax_exit,
            "expected": len(ax_expected),
            "reported": len(ax_cones),
            "missing": ax_missing,
            "out_of_cone": ax_bad,
            "seconds": ax_secs,
            "log": ax_log,
        },
        "mutations": {
            "poisoned_audit": {
                "file": MUT_POISON,
                "sha256": sha(os.path.join(ROOT, MUT_POISON)),
                "compile_exit": mut_a_exit,
                "reported_cones": mut_a_cones,
                "violations": mut_a_viol,
                "log": mut_a_log,
            },
            "truncated_audit": {
                "file": MUT_TRUNC,
                "sha256": sha(os.path.join(ROOT, MUT_TRUNC)),
                "compile_exit": mut_b_exit,
                "reported": len(mut_b_cones),
                "source_expected": len(mut_b_src_expected),
                "naive_check_would_pass": naive_would_pass,
                "coverage_uncovered": len(mut_b_uncovered),
                "log": mut_b_log,
            },
            "scan_targets": {
                "dir": MUT_SCAN_DIR,
                "scanner_exit": scan_exit,
                "hard_match_count": scan and scan.get("hard_match_count"),
                "hard_files": hard_files,
                "soft_files": soft_files,
                "log": scan_log,
            },
        },
        "release_scan": {
            "hard_match_count": rel_scan and rel_scan.get("hard_match_count"),
            "lean_files_scanned": rel_scan and rel_scan.get("lean_files_scanned"),
            "log": rel_log,
        },
        "deliverable_hashes": {rel: sha(os.path.join(ROOT, rel)) for rel in CHECKPOINT_CORE},
        "checks": checks,
    }
    out_path = os.path.join(EV, "acceptance-pass6.json")
    with open(out_path, "w") as f:
        json.dump(report, f, indent=1)
    print(f"\nverdict: {verdict} -> {os.path.relpath(out_path, ROOT)}")
    return 0 if verdict == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
