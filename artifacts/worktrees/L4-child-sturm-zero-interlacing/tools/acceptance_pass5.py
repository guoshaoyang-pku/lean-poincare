#!/usr/bin/env python3
"""
Pass-5 independent acceptance check for `L4-child-sturm-zero-interlacing`.

Continuation invocation (2026-09-12).  This driver is independent of
`tools/run_sturm_gates.py`, `tools/acceptance_pass2.py`, `tools/acceptance_pass3.py` and
`tools/gs_independent_check.py`: it uses its own probe `tmp/acceptance_probe_r5.lean` and
re-derives the release-level facts from the files on disk.  It adds one check the earlier
passes do not perform: **proof-term provenance**.  `#print` of the engine-consuming
declarations is parsed out of the elaboration output and each declaration's *elaborated proof
term* must mention the D12 engine declaration it is advertised to consume
(`sturm_zero_comparison`, `sturm_zero_comparison_of_pos`, `sign_constant_of_no_zero`,
`wronskian_deriv`, `wronskian_antitoneOn_of_le`, `wronskian_continuousOn`,
`wronskian_differentiableOn`).  This is stronger than a source grep: it inspects what the
kernel actually elaborated.

Fail-closed gates:

  1. full project-closure rebuild: every project `.olean` under
     `release/.lake/build/lib/lean/Poincare` is deleted, then the three deliverable modules
     are rebuilt with `lake build` (exit 0, jobs > 0); the `.lean` sources are byte-identical
     before and after;
  2. the fresh pass-5 probe compiles against the rebuilt oleans (exit 0, no `error`);
  3. every `#print axioms` line of the probe is reported exactly once and its cone is a
     subset of {propext, Classical.choice, Quot.sound} (no `sorryAx`);
  4. proof-term provenance: the `#print` blocks of the seven engine-consuming declarations are
     found and each mentions its required engine declarations (name-boundary match);
  5. the probe source contains no `sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`partial`/
     `native_decide` token;
  6. the axiom-audit module re-run on the rebuilt oleans reports all expected declarations
     with cones inside the allowed set, and covers every declaration of the two deliverable
     modules;
  7. the five deliverable files match the hashes recorded in the result card;
  8. all 13 read-only inputs are byte-identical to the leader release;
  9. the main deliverable module neither imports `ConjugatePointBound` nor mentions
     `conjugate_point_bound` in code (comments stripped);
 10. no declaration name in the two deliverable modules collides with a declaration of the
     imported prior art or of the leader release tree;
 11. the card verdict is TASK_DONE (JSON and markdown), and the checkpoint history is intact
     with the latest entry's gates PASS;
 12. inherited shared files (`manifest/`, `input/`, `longrun/`) were not modified during the
     task.

Outputs `evidence/acceptance-pass5.json`; exits nonzero on any failure.
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

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PROBE = "tmp/acceptance_probe_r5.lean"
PROBE_LOG = "75_pass5_probe.log"
AUDIT_LOG = "76_pass5_audit.log"
CLOSURE_LOG = "74_pass5_closure_rebuild.log"

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

CARD_MODULES = {
    "core": CORE, "cross_check": CROSS, "axiom_audit": AUDIT,
    "negative_control": NEG, "gate_driver": "tools/run_sturm_gates.py",
}

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

# declaration -> engine declarations its elaborated proof term must mention
PROVENANCE = {
    "exists_zero_of_curvature_lt": ["sturm_zero_comparison"],
    "exists_jacobi_zero_on_Ioc_pi_sqrt": ["sturm_zero_comparison"],
    "sturm_dichotomy_of_interior_bound": ["sturm_zero_comparison_of_pos",
                                          "sign_constant_of_no_zero"],
    "eq_zero_at_pi_sqrt_of_curvature_eq": ["wronskian_deriv", "wronskian_continuousOn",
                                           "wronskian_differentiableOn"],
    "wronskian_sin_linear_antitoneOn": ["wronskian_antitoneOn_of_le"],
    "wronskian_deriv_sin_linear": ["wronskian_deriv"],
    "no_positive_solution_past_pi_sqrt": ["sturm_dichotomy_of_interior_bound"],
}

DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable def|def|abbrev|instance|structure|class)\s+"
    r"([A-Za-z0-9_'.]+)", re.M)
HEADER_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable def|def|abbrev|instance|structure|class)\s+"
    r"Poincare\.L4\.GeodesicComparison\.([A-Za-z0-9_']+)", re.M)

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
    flat = re.sub(r"\s+", " ", text)
    out = {}
    pat = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|"
                     r"does not depend on any axioms)")
    for m in pat.finditer(flat):
        out[m.group(1)] = [a.strip() for a in m.group(2).split(",")] if m.group(2) else []
    return out


def lean_tree_hashes():
    out = {}
    for dirpath, dirnames, filenames in os.walk(RELEASE):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                out[os.path.relpath(p, ROOT)] = sha(p)
    return out


def run_logged(cmd, log_name, timeout=3600):
    log_path = os.path.join(LOGS, log_name)
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {' '.join(cmd)}\n# cwd: {RELEASE}\n\n")
        log.flush()
        p = subprocess.run(cmd, cwd=RELEASE, stdout=log, stderr=subprocess.STDOUT,
                           env=ENV, timeout=timeout)
    return (p.returncode, open(log_path).read(), round(time.time() - t0, 2),
            os.path.relpath(log_path, ROOT))


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--.*", " ", text)
    return text


def exact_name_hits(text, name):
    return len(re.findall(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", text))


def main():
    started = datetime.now(timezone.utc).isoformat()
    cp = json.load(open(os.path.join(ROOT, "checkpoint.json")))
    cp1_at = cp["checkpoints"][0]["at"]

    # ---- 1. full project-closure rebuild --------------------------------
    src_before = lean_tree_hashes()
    oleans_deleted = 0
    if os.path.isdir(BUILD_ROOT):
        for dirpath, _dirnames, filenames in os.walk(BUILD_ROOT):
            oleans_deleted += sum(1 for fn in filenames
                                  if fn.endswith((".olean", ".ilean", ".trace")))
        shutil.rmtree(BUILD_ROOT)
    clo_exit, clo_out, clo_secs, clo_log = run_logged(
        ["lake", "build"] + MODULES, CLOSURE_LOG)
    m = re.search(r"Build completed successfully \((\d+) jobs\)", clo_out)
    jobs = int(m.group(1)) if m else -1
    src_after = lean_tree_hashes()
    differing = [k for k in src_before if src_before.get(k) != src_after.get(k)]
    check("closure_rebuild_exit0_jobs", clo_exit == 0 and jobs > 0,
          f"exit={clo_exit} jobs={jobs} oleans_deleted={oleans_deleted} "
          f"seconds={clo_secs} log={clo_log}")
    check("closure_rebuild_left_sources_unchanged", not differing,
          f"lean_files={len(src_before)} differing={differing[:3]}")

    # ---- 2. compile the fresh pass-5 probe ------------------------------
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

    # ---- 4. proof-term provenance --------------------------------------
    blocks = {}
    marks = list(HEADER_RE.finditer(probe_out))
    for i, mm in enumerate(marks):
        end = marks[i + 1].start() if i + 1 < len(marks) else len(probe_out)
        blocks[mm.group(1)] = probe_out[mm.start():end]
    prov_rows = []
    prov_ok = True
    for decl, engines in PROVENANCE.items():
        block = blocks.get(decl, "")
        hits = {e: exact_name_hits(block, e) for e in engines}
        row_ok = bool(block) and all(hits[e] > 0 for e in engines)
        prov_ok = prov_ok and row_ok
        prov_rows.append({"declaration": decl, "engine_hits": hits, "ok": row_ok,
                          "block_chars": len(block)})
    check("proof_term_provenance_engine_consumption",
          prov_ok and len(blocks) >= len(PROVENANCE),
          f"declarations={len(PROVENANCE)} printed_blocks={len(blocks)} "
          f"failures={[r['declaration'] for r in prov_rows if not r['ok']]}")

    # ---- 5. probe source hygiene ---------------------------------------
    tokens = sorted(set(re.findall(
        r"\b(sorry|admit|axiom|unsafe|opaque|partial|native_decide)\b", probe_src)))
    check("probe_source_no_forbidden_tokens", not tokens, f"tokens={tokens}")

    # ---- 6. axiom-audit module re-run on the rebuilt oleans -------------
    ax_exit, ax_out, ax_secs, ax_log = run_logged(
        ["lake", "env", "lean", AUDIT_REL], AUDIT_LOG, timeout=1800)
    ax_expected = re.findall(r"#print axioms (\S+)", open(os.path.join(ROOT, AUDIT)).read())
    ax_cones = parse_cones(ax_out)
    ax_missing = [d for d in ax_expected if d not in ax_cones]
    ax_bad = {d: c for d, c in ax_cones.items() if not set(c) <= ALLOWED}
    ax_sorry = [d for d, c in ax_cones.items() if "sorryAx" in c]
    check("audit_rerun_all_in_cone",
          ax_exit == 0 and not ax_missing and not ax_bad and not ax_sorry,
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

    # ---- 7. deliverable hashes against the card -------------------------
    card = json.load(open(os.path.join(ROOT, CARD_JSON)))
    mism = []
    for key, rel in CARD_MODULES.items():
        p = os.path.join(ROOT, rel)
        if not os.path.exists(p) or sha(p) != card["module_hashes"].get(key):
            mism.append(key)
    check("deliverable_hashes_match_card", not mism, f"mismatched={mism}")

    # ---- 8. read-only inputs byte-identical to the leader release -------
    ih_mism = []
    for rel in INPUT_FILES:
        a, b = os.path.join(RELEASE, rel), os.path.join(LEADER, rel)
        if not (os.path.exists(a) and os.path.exists(b) and sha(a) == sha(b)):
            ih_mism.append(rel)
    check("inputs_byte_identical_to_leader", not ih_mism,
          f"files={len(INPUT_FILES)} mismatched={ih_mism}")

    # ---- 9. no assumption of the cross-checked prior result -------------
    core_src = open(os.path.join(ROOT, CORE)).read()
    imports = re.findall(r"^import\s+(\S+)", core_src, re.M)
    imports_cpb = [i for i in imports if "ConjugatePointBound" in i]
    code = strip_comments(core_src)
    mentions = exact_name_hits(code, "conjugate_point_bound")
    check("main_module_does_not_assume_conjugate_point_bound",
          not imports_cpb and mentions == 0,
          f"imports={imports} conjugate_point_bound_in_code={mentions}")

    # ---- 10. declaration-name collisions --------------------------------
    prior = set()
    for rel in ("release/Poincare/L4/GeodesicComparison/SturmZeroCount.lean",
                "release/Poincare/L4/GeodesicComparison/ConjugatePointBound.lean"):
        prior |= set(DECL_RE.findall(open(os.path.join(ROOT, rel)).read()))
    leader = set()
    for dirpath, dirnames, filenames in os.walk(LEADER):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if fn.endswith(".lean"):
                leader |= set(DECL_RE.findall(open(os.path.join(dirpath, fn)).read()))
    col_prior = sorted(own & prior)
    col_leader = sorted(own & leader)
    check("no_prior_art_or_leader_name_collisions", not col_prior and not col_leader,
          f"own={len(own)} prior_collisions={col_prior[:5]} "
          f"leader_collisions={col_leader[:5]}")

    # ---- 11. card verdict and checkpoint integrity ----------------------
    md = open(os.path.join(ROOT, CARD_MD)).read()
    card_ok = (card.get("verdict") == "TASK_DONE" and md.rstrip().endswith("**TASK_DONE**"))
    check("card_verdict_task_done", card_ok,
          f"json_verdict={card.get('verdict')} md_ends_task_done="
          f"{md.rstrip().endswith('**TASK_DONE**')}")
    ids = [c["id"] for c in cp["checkpoints"]]
    cps_ok = (len(ids) >= 21 and len(set(ids)) == len(ids)
              and cp["checkpoints"][-1].get("gates") == "PASS"
              and cp.get("current", {}).get("latest") == ids[-1])
    check("checkpoint_history_intact_latest_gates_pass", cps_ok,
          f"entries={len(ids)} unique={len(set(ids))} latest={ids[-1]} "
          f"gates={cp['checkpoints'][-1].get('gates')}")

    # ---- 12. inherited shared files preserved ---------------------------
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
        "schema": "l4-child-sturm-zero-interlacing/acceptance-pass5-v1",
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
            "provenance": prov_rows,
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
        "deliverable_hashes": {k: sha(os.path.join(ROOT, v))
                               for k, v in CARD_MODULES.items()},
        "checks": checks,
    }
    out_path = os.path.join(EV, "acceptance-pass5.json")
    with open(out_path, "w") as f:
        json.dump(report, f, indent=1)
    print(f"\nverdict: {verdict} -> {os.path.relpath(out_path, ROOT)}")
    return 0 if verdict == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
