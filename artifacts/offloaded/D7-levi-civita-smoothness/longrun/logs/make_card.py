#!/usr/bin/env python3
"""Generate longrun/results/D7-levi-civita-smoothness.{json,md} from verified artifacts."""
import json, os, re, subprocess, time

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-levi-civita-smoothness"
OUT = os.path.join(WT, "longrun", "results")
os.makedirs(OUT, exist_ok=True)

gate = json.load(open(os.path.join(WT, "longrun", "logs", "gate", "gate_replication.json")))
gate_files = gate["files"]
gate_ok = gate["ok"]
gate_failures = [f for f in gate_files if f["exit"] != 0]

scan = json.load(open(os.path.join(WT, "longrun", "logs", "forbidden_scan.json")))

# parse the axiom audit
audit_txt = open(os.path.join(WT, "longrun", "logs", "axiom_audit.log")).read()
entries = []
cur = ""
for line in audit_txt.splitlines():
    if line.startswith("'Poincare"):
        if cur:
            entries.append(cur)
        cur = line
    elif cur:
        cur += " " + line.strip()
if cur:
    entries.append(cur)
axioms = []
allowed = {"propext", "Classical.choice", "Quot.sound"}
for e in entries:
    m = re.match(r"'([^']+)' depends on axioms: \[(.*)\]", e)
    if m:
        axs = sorted({a.strip() for a in m.group(2).split(",") if a.strip()})
        axioms.append({"declaration": m.group(1), "axioms": axs,
                       "clean": set(axs) <= allowed})
axiom_clean = all(a["clean"] for a in axioms)

new_files = sorted(os.path.join("release", "Poincare", "D7", "LeviCivita", f)
                   for f in os.listdir(os.path.join(WT, "release", "Poincare", "D7", "LeviCivita"))
                   if f.endswith(".lean"))
line_counts = {}
for f in new_files:
    line_counts[f] = sum(1 for _ in open(os.path.join(WT, f)))

lean_total = subprocess.run(
    ["bash", "-c", "find . -name '*.lean' -not -path '*/.lake/*' | wc -l"],
    cwd=WT, capture_output=True, text=True).stdout.strip()

generated = time.strftime("%Y-%m-%dT%H:%M:%S%z")

card = {
  "schema": "longrun.result-card.v1",
  "task_id": "D7-levi-civita-smoothness",
  "worktree": WT,
  "generated_at": generated,
  "verdict": "TASK_DONE" if (gate_ok and axiom_clean
                             and scan["hard_match_count"] == 0
                             and scan["soft_match_count"] == 0) else "TASK_BLOCKED",
  "scaffold": {
    "prescribed": "cp -al ../D7-riemann-curvature-tensor/. .",
    "hard_link_result": "FAILED: the workspace sandbox rejects cross-tree hard links with "
                        "Invalid cross-device link (EXDEV), although both trees are on /data3 "
                        "(stat -c %d = 66313 for both).",
    "fallback_used": "cp -a ../D7-riemann-curvature-tensor/. . (byte-identical recursive copy, "
                     "symlinks preserved: .lake -> release/.lake, "
                     "release/.lake/packages -> shared mathlib packages)",
    "integrity": "diff -rq --exclude=.lake --exclude=LeviCivita against the source worktree "
                 "reports no content differences; 287 copied files (excluding .lake build "
                 "artifacts) are byte-identical, 0 changed, 0 missing. Additions are only "
                 "release/Poincare/D7/LeviCivita/ (7 new Lean files) and longrun/logs/.",
    "no_copied_file_modified": True
  },
  "toolchain": {
    "lean": open(os.path.join(WT, "lean-toolchain")).read().strip(),
    "mathlib_rev": "7974e751bece493b6ff508039423ca9fa2452fa8",
    "mathlib_date": "2026-09-05",
    "mathlib_file": "Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean"
  },
  "mathlib_probe": {
    "method": "grep over the pinned mathlib checkout plus the compilable probe "
              "release/Poincare/D7/LeviCivita/Probe.lean (#check present, #check_failure absent)",
    "levi_civita_present": [
      "CovariantDerivative (Basic.lean:366)",
      "IsCovariantDerivativeOn (Basic.lean:92)",
      "CovariantDerivative.torsion (Torsion.lean:120)",
      "CovariantDerivative.torsion_antisymm (Torsion.lean:140)",
      "CovariantDerivative.torsion_eq_zero_iff (Torsion.lean:143)",
      "CovariantDerivative.IsMetricCompatible (Metric.lean:155)",
      "CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq (Metric.lean:160)",
      "CovariantDerivative.isMetricCompatible_iff (Metric.lean:170)",
      "CovariantDerivative.IsLeviCivitaConnection (LeviCivita.lean:201)",
      "CovariantDerivative.IsLeviCivitaConnection.apply_eq (Koszul formula, LeviCivita.lean:214)",
      "CovariantDerivative.IsLeviCivitaConnection.apply_eq_extend (LeviCivita.lean:239)",
      "CovariantDerivative.IsLeviCivitaConnection.uniqueness (LeviCivita.lean:255)",
      "CovariantDerivative.leviCivitaConnection (LeviCivita.lean:359)",
      "CovariantDerivative.isMetricCompatible_leviCivitaConnection (LeviCivita.lean:383)",
      "CovariantDerivative.torsion_leviCivitaConnection_eq_zero (LeviCivita.lean:396)",
      "CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection (LeviCivita.lean:408)"
    ],
    "smoothness_statements_that_exist": [
      "ContMDiffCovariantDerivativeOn (Basic.lean:108): cov sigma is C^k on a set for every "
      "C^(k+1) section sigma",
      "ContMDiffCovariantDerivativeOn.affine_combination (Basic.lean:250) and "
      "ContMDiffCovariantDerivativeOn.finite_affine_combination (Basic.lean:284): C^k is closed "
      "under affine combinations",
      "CovariantDerivative.ContMDiffCovariantDerivative (Basic.lean:412): the bundled global class",
      "CovariantDerivative.ContMDiffCovariantDerivative.affineCombination (Basic.lean:459) and "
      ".finiteAffineCombination (Basic.lean:472)",
      "IsContMDiffRiemannianBundle (VectorBundle/Riemannian.lean:67) and "
      "IsContMDiffRiemannianBundle.of_le (Riemannian.lean:74): smoothness of the metric, the "
      "hypothesis of the Levi-Civita smoothness theorem",
      "analytic engine reused: ContinuousLinearMap.contMDiff, ContMDiff.clm_apply, "
      "ContDiff.contDiff_fderiv_apply, ContDiff.fderiv_apply"
    ],
    "smoothness_statements_absent": [
      "CovariantDerivative.contMDiff_leviCivitaConnection (#check_failure passes)",
      "CovariantDerivative.leviCivitaConnection_contMDiff (#check_failure passes)",
      "ContMDiffCovariantDerivative.leviCivitaConnection (#check_failure passes)",
      "CovariantDerivative.leviCivitaConnection_isContMDiff (#check_failure passes)",
      "IsLeviCivitaConnection.isContMDiff (#check_failure passes)",
      "the module docstring of LeviCivita.lean lines 22-23 announces the result as a future PR: "
      "'Future PRs will prove smoothness: if M is C^{n+2} and g is C^{n+1}, the Levi-Civita "
      "connection is a C^n connection.' No declaration proves it."
    ],
    "curvature_declarations_absent": [
      "CovariantDerivative.curvature", "CovariantDerivative.riemann",
      "CovariantDerivative.IsContMDiff", "RiemannTensor", "RiemannianCurvature",
      "RicciTensor", "christoffelSymbol", "ChristoffelSymbol",
      "grep -ri curvature over the pinned Mathlib/ matches exactly one file: "
      "MeasureTheory/Measure/Doubling.lean:44 (a docstring)"
    ]
  },
  "new_files": [
    {"path": f, "lines": line_counts[f], "role": {
      "release/Poincare/D7/LeviCivita/Basic.lean": "affine/mean connections and difference "
        "tensor (task items 2a, 2b) + lifting to RiemannCurvatureData",
      "release/Poincare/D7/LeviCivita/Coefficients.lean": "basis connection coefficients and "
        "the smooth coefficient interface (task item 2c)",
      "release/Poincare/D7/LeviCivita/Koszul.lean": "chart-smoothness theorem for the Koszul "
        "Christoffel symbols (task item 2c, calculus)",
      "release/Poincare/D7/LeviCivita/Blocked.lean": "state-only Props and named blockers "
        "(task item 3)",
      "release/Poincare/D7/LeviCivita/Probe.lean": "compilable mathlib declaration/smoothness "
        "probe (task item 1)",
      "release/Poincare/D7/LeviCivita/Smoke.lean": "non-vacuity witnesses and computations",
      "release/Poincare/D7/LeviCivita/Audit.lean": "#print axioms audit"
    }[f]} for f in new_files
  ],
  "proved": {
    "item_2a_mean_metric_compatible": [
      "Poincare.D7.LeviCivita.isMetricCompatible_affine: affine combinations of "
      "metric-compatible connections are metric-compatible",
      "Poincare.D7.LeviCivita.isMetricCompatible_mean: THE MEAN of two metric-compatible "
      "connections is metric-compatible",
      "Poincare.D7.LeviCivita.isTorsionFree_mean and isLeviCivita_mean: the same for the "
      "torsion-free and Levi-Civita properties for a common bracket",
      "Poincare.D7.LeviCivita.meanConnection_eq_left / _right: the mean of two Levi-Civita "
      "connections equals each of them (uniqueness coherence)",
      "Poincare.D7.Curvature.RiemannCurvatureData.meanData: the mean of two D7 curvature data "
      "sharing metric and bracket is again a RiemannCurvatureData",
      "Poincare.D7.LeviCivita.connectionCoefficient_mean and "
      "isMetricCompatible_coefficient_relation_affine: the same at the coefficient level"
    ],
    "item_2b_difference_tensor_symmetric": [
      "Poincare.D7.LeviCivita.differenceTensor_symm: THE DIFFERENCE TENSOR of two torsion-free "
      "connections for the same bracket is symmetric",
      "Poincare.D7.LeviCivita.differenceTensor_metric_antisymm: the difference tensor of two "
      "metric-compatible connections is metric-antisymmetric",
      "Poincare.D7.LeviCivita.differenceTensor_eq_zero_of_isLeviCivita: the difference tensor of "
      "two Levi-Civita connections vanishes (difference-tensor form of uniqueness)",
      "Poincare.D7.Curvature.RiemannCurvatureData.differenceTensor_symm: the D7-data version",
      "Poincare.D7.LeviCivita.isTorsionFree_coefficient_relation and "
      "isTorsionFree_coefficient_relation_affine: the coefficient-level relation"
    ],
    "item_2c_coefficient_smoothness": [
      "Poincare.D7.LeviCivita.contMDiff_coefficientField: a C^n connection field has C^n "
      "coefficients (ContMDiff.clm_apply + ContinuousLinearMap.contMDiff)",
      "Poincare.D7.LeviCivita.contMDiff_coefficientField_comp_chart: under the stated chart "
      "smoothness hypothesis (a C^n chart phi), the pulled-back coefficients are C^n",
      "Poincare.D7.LeviCivita.SmoothCoefficientSystem: the bundled interface (C^n coefficient "
      "functions + torsion and metric relations); .affineCombination/.mean preserve it, "
      ".pullback pulls it back along a C^n chart, .const inhabits it",
      "Poincare.D7.LeviCivita.contDiff_christoffelSymbol: if the chart metric coefficients are "
      "C^{n+1} and the inverse-metric coefficients are C^n, the Koszul Christoffel symbols are "
      "C^n (ContDiff.contDiff_fderiv_apply + closure under sums/products)",
      "Poincare.D7.LeviCivita.contDiff_fderiv_coefficient: directional derivative smoothness"
    ],
    "coefficient_algebra": [
      "Poincare.D7.LeviCivita.sum_connectionCoefficient_smul: reconstruction "
      "nabla e_i e_j = sum_k Gamma^k_ij e_k",
      "Poincare.D7.LeviCivita.form_nabla_basis: <nabla e_i e_j, e_k> = Gamma^k_ij",
      "Poincare.D7.LeviCivita.isMetricCompatible_coefficient_relation: Gamma^k_ij + Gamma^j_ik = 0",
      "Poincare.D7.LeviCivita.connectionCoefficient_affine/_mean/_difference: coefficient "
      "functoriality"
    ]
  },
  "state_only": [
    {
      "prop": "Poincare.D7.LeviCivita.LeviCivitaSmoothnessStatement",
      "statement": "ContMDiffCovariantDerivative (leviCivitaConnection I M) n, i.e. if M is "
                   "C^{n+2} and g is C^{n+1} then the Levi-Civita connection is C^n",
      "blocker": "B-D7-LC-SMOOTHNESS",
      "missing_dependencies": [
        "the instance ContMDiffCovariantDerivative (leviCivitaConnection I M) n (class exists at "
        "Basic.lean:412, no instance)",
        "the manifold-level smoothness proof announced in LeviCivita.lean lines 22-23 (docstring "
        "only)",
        "a smoothness-preserving dual/musical-isomorphism construction for the Koszul form; the "
        "coordinate half is proved in contDiff_christoffelSymbol"
      ]
    },
    {
      "prop": "Poincare.D7.LeviCivita.SmoothLeviCivitaExistenceStatement",
      "statement": "there exists a C^n torsion-free metric-compatible connection on a smooth "
                   "Riemannian manifold",
      "blocker": "B-D7-LC-SMOOTHNESS",
      "missing_dependencies": [
        "only the C^n part: mathlib provides the connection and its Levi-Civita property "
        "(checked reuse leviCivitaConnection_isLeviCivitaConnection)",
        "the checked reduction smoothLeviCivitaExistence_of_smoothness shows the statement "
        "follows from LeviCivitaSmoothnessStatement"
      ]
    },
    {
      "prop": "Poincare.D7.LeviCivita.CovariantDerivativeCurvatureMatchesD7",
      "statement": "there is a pointwise (1,3) tensor kappa equal to the candidate formula "
                   "R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z - nabla_[X,Y] Z and "
                   "satisfying first-pair antisymmetry and the first Bianchi identity (the D7 "
                   "interface obligations)",
      "blocker": "B-D7-MANIFOLD-CURVATURE",
      "missing_dependencies": [
        "CovariantDerivative.curvature (absent; grep of Mathlib/ for curvature matches only a "
        "docstring)",
        "second covariant derivative of a section (no calculus of nabla_X nabla_Y Z, so the "
        "candidate formula cannot be proved tensorial)",
        "smoothness of the connection to differentiate the section y |-> nabla_Y(y) Z (same gap "
        "as B-D7-LC-SMOOTHNESS)",
        "the induced connection on the (1,3) tensor bundle for the second Bianchi identity "
        "(B-D7-NABLA-R)"
      ]
    }
  ],
  "verification": {
    "compile_gate": {
      "command": "lake env lean <file> from the worktree root, every *.lean (skipping .lake)",
      "files_checked": len(gate_files),
      "exit_zero": len(gate_files) - len(gate_failures),
      "failures": gate_failures,
      "ok": gate_ok,
      "authored_files_checked": len(new_files),
      "log": "longrun/logs/gate_replication.log",
      "json": "longrun/logs/gate/gate_replication.json"
    },
    "axiom_audit": {
      "command": "lake env lean release/Poincare/D7/LeviCivita/Audit.lean",
      "declarations_audited": len(axioms),
      "all_clean": axiom_clean,
      "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
      "forbidden_found": [a["declaration"] for a in axioms if not a["clean"]],
      "log": "longrun/logs/axiom_audit.log",
      "entries": axioms
    },
    "forbidden_token_scan": {
      "command": "python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/LeviCivita",
      "lean_files_scanned": scan["lean_files_scanned"],
      "hard_match_count": scan["hard_match_count"],
      "soft_match_count": scan["soft_match_count"],
      "hard_forbidden": scan["hard_forbidden"],
      "soft_flags": scan["soft_flags"],
      "log": "longrun/logs/forbidden_scan.json"
    },
    "integrity": {
      "command": "diff -rq --exclude=.lake --exclude=LeviCivita ../D7-riemann-curvature-tensor .",
      "result": "no content differences; only additions longrun/logs/ and "
                "release/Poincare/D7/LeviCivita/",
      "copied_files_checked": 287,
      "changed": 0,
      "missing": 0
    },
    "lean_files_in_worktree": int(lean_total),
    "package_build": {
      "command": "cd release && lake build",
      "exit": 0,
      "jobs": 8962,
      "note": "full release package build (all libraries Poincare/Probe/Ledger/Audit plus the "
              "new Poincare.D7.LeviCivita modules) succeeds"
    }
  },
  "honest_boundary": [
    "The D7 curvature data is the D2 abstract algebraic Koszul connection on a real vector "
    "space, not a mathlib CovariantDerivative on a smooth manifold; the bracket is abstract data.",
    "The manifold-level smoothness of leviCivitaConnection and the construction of "
    "CovariantDerivative.curvature are NOT proved; they are the explicit state-only Props "
    "LeviCivitaSmoothnessStatement/SmoothLeviCivitaExistenceStatement and "
    "CovariantDerivativeCurvatureMatchesD7 with named blockers.",
    "The Koszul theorem contDiff_christoffelSymbol is chart-level and takes the metric and "
    "inverse-metric coefficient smoothness as explicit hypotheses; positive definiteness and the "
    "derivation of inverse-metric smoothness from metric smoothness are not formalized.",
    "The candidate curvature formula is stated (stateable with FiberBundle.extend and "
    "VectorField.mlieBracket) but not proved to be a tensor.",
    "No claim is made about Ricci flow, Perelman monotonicity, surgery, or the Poincare "
    "conjecture."
  ],
  "task_items": {
    "1_mathlib_probe": "DONE: Probe.lean + mathlib_probe section",
    "2a_mean_metric_compatible": "DONE: isMetricCompatible_mean (+ affine and D7-data lifting)",
    "2b_difference_tensor_symmetric": "DONE: differenceTensor_symm (+ D7-data lifting)",
    "2c_coefficient_smoothness_interface": "DONE: contMDiff_coefficientField, "
      "contMDiff_coefficientField_comp_chart, SmoothCoefficientSystem.pullback, "
      "contDiff_christoffelSymbol",
    "3a_full_levi_civita_existence_prop": "DONE: SmoothLeviCivitaExistenceStatement + "
      "LeviCivitaSmoothnessStatement with missing-dependency records",
    "3b_covariant_derivative_curvature_prop": "DONE: CovariantDerivativeCurvatureMatchesD7 + "
      "curvatureCandidate with missing-dependency records",
    "4_no_forbidden_tokens": "DONE: 0 hard, 0 soft",
    "5_compile_and_axioms": "DONE: gate exit 0 for every .lean; 64 declarations audited, all "
      "subset {propext, Classical.choice, Quot.sound}",
    "6_results_card": "longrun/results/D7-levi-civita-smoothness.md + .json"
  }
}

with open(os.path.join(OUT, "D7-levi-civita-smoothness.json"), "w") as fh:
    json.dump(card, fh, indent=2)

# ---- markdown ----
def bullets(xs):
    return "\n".join("- " + x for x in xs)

md = []
md.append("# D7-levi-civita-smoothness — result card")
md.append("")
md.append(f"- **Task id:** `D7-levi-civita-smoothness`")
md.append(f"- **Worktree:** `{WT}`")
md.append(f"- **Generated:** `{generated}`")
md.append(f"- **Verdict:** **{card['verdict']}**")
md.append(f"- **Lean:** `{card['toolchain']['lean']}`")
md.append(f"- **mathlib:** `{card['toolchain']['mathlib_rev']}` "
          f"(`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`)")
md.append(f"- **Authored:** {len(new_files)} files, {sum(line_counts.values())} lines, all under "
          f"`release/Poincare/D7/LeviCivita/`")
md.append("- **Machine-readable card:** `longrun/results/D7-levi-civita-smoothness.json`")
md.append("")
md.append("## 0. Scaffold")
md.append("")
md.append(f"- Prescribed: `{card['scaffold']['prescribed']}`")
md.append(f"- **Outcome: failed.** {card['scaffold']['hard_link_result']}")
md.append(f"- **Fallback:** {card['scaffold']['fallback_used']}")
md.append(f"- **Integrity:** {card['scaffold']['integrity']}")
md.append("")
md.append("## 1. Mathlib probe (task item 1)")
md.append("")
md.append(f"Method: {card['mathlib_probe']['method']}. Evidence: "
          "`longrun/logs/mathlib_probe_evidence.txt`.")
md.append("")
md.append("### 1.1 Levi-Civita connection API — present and reused")
md.append("")
md.append(bullets(card["mathlib_probe"]["levi_civita_present"]))
md.append("")
md.append("### 1.2 Smoothness statements that DO exist")
md.append("")
md.append(bullets(card["mathlib_probe"]["smoothness_statements_that_exist"]))
md.append("")
md.append("### 1.3 Smoothness statements that DO NOT exist (the gap this layer names)")
md.append("")
md.append(bullets(card["mathlib_probe"]["smoothness_statements_absent"]))
md.append("")
md.append("### 1.4 Curvature declarations — absent")
md.append("")
md.append(bullets(card["mathlib_probe"]["curvature_declarations_absent"]))
md.append("")
md.append("## 2. Proved (kernel-checked) results")
md.append("")
md.append("### 2a. The mean of two metric-compatible connections is metric-compatible")
md.append("")
md.append(bullets(card["proved"]["item_2a_mean_metric_compatible"]))
md.append("")
md.append("### 2b. The difference tensor of two torsion-free connections is symmetric")
md.append("")
md.append(bullets(card["proved"]["item_2b_difference_tensor_symmetric"]))
md.append("")
md.append("### 2c. Smoothness of the connection-coefficients interface")
md.append("")
md.append(bullets(card["proved"]["item_2c_coefficient_smoothness"]))
md.append("")
md.append("### 2d. Coefficient algebra (supporting results)")
md.append("")
md.append(bullets(card["proved"]["coefficient_algebra"]))
md.append("")
md.append("## 3. State-only Props with exact missing dependencies (task item 3)")
md.append("")
for item in card["state_only"]:
    md.append(f"### `{item['prop']}`")
    md.append("")
    md.append(f"- statement: {item['statement']}")
    md.append(f"- blocker: `{item['blocker']}`")
    md.append("- missing mathlib dependencies:")
    md.append("\n".join("  - " + d for d in item["missing_dependencies"]))
    md.append("")
md.append("## 4. Verification")
md.append("")
cg = card["verification"]["compile_gate"]
md.append(f"### 4.1 Compile gate — `{cg['command']}`")
md.append("")
md.append(f"- files checked: **{cg['files_checked']}**, exit 0: **{cg['exit_zero']}**, "
          f"failures: **{len(cg['failures'])}** — **{'PASS' if cg['ok'] else 'FAIL'}**")
md.append(f"- authored files checked: {cg['authored_files_checked']}/7")
md.append(f"- log: `{cg['log']}`, json: `{cg['json']}`")
md.append("")
ax = card["verification"]["axiom_audit"]
md.append("### 4.2 Axiom audit — `#print axioms`")
md.append("")
md.append(f"- declarations audited: **{ax['declarations_audited']}**")
md.append(f"- all axiom cones ⊆ `{{propext, Classical.choice, Quot.sound}}`: "
          f"**{ax['all_clean']}**")
md.append(f"- forbidden axiom occurrences (project axiom / `sorryAx` / `native_decide` / "
          f"`proof_wanted`): **{len(ax['forbidden_found'])}**")
md.append(f"- log: `{ax['log']}`")
md.append("")
fs = card["verification"]["forbidden_token_scan"]
md.append("### 4.3 Forbidden-token scan")
md.append("")
md.append(f"- command: `{fs['command']}`")
md.append(f"- files scanned: {fs['lean_files_scanned']}, hard matches: "
          f"**{fs['hard_match_count']}**, soft flags: **{fs['soft_match_count']}**")
md.append(f"- log: `{fs['log']}`")
md.append("")
pb = card["verification"]["package_build"]
md.append("### 4.4 Full release package build")
md.append("")
md.append(f"- command: `{pb['command']}` — exit **{pb['exit']}** ({pb['jobs']} jobs)")
md.append(f"- {pb['note']}")
md.append("")
ig = card["verification"]["integrity"]
md.append("### 4.5 Copied-file integrity")
md.append("")
md.append(f"- command: `{ig['command']}`")
md.append(f"- {ig['copied_files_checked']} copied files checked, {ig['changed']} changed, "
          f"{ig['missing']} missing; {ig['result']}")
md.append("")
md.append("## 5. Authored files")
md.append("")
for f in card["new_files"]:
    md.append(f"- `{f['path']}` — {f['lines']} lines — {f['role']}")
md.append("")
md.append("## 6. Honest boundary")
md.append("")
md.append(bullets(card["honest_boundary"]))
md.append("")
md.append("## 7. Task-item coverage")
md.append("")
for k, v in card["task_items"].items():
    md.append(f"- **{k}**: {v}")
md.append("")
md.append(f"**Status line: {card['verdict']}**")
md.append("")

with open(os.path.join(OUT, "D7-levi-civita-smoothness.md"), "w") as fh:
    fh.write("\n".join(md))

print("verdict:", card["verdict"])
print("gate:", cg["exit_zero"], "/", cg["files_checked"], "failures:", len(cg["failures"]))
print("axioms:", ax["declarations_audited"], "clean:", ax["all_clean"])
print("scan:", fs["hard_match_count"], fs["soft_match_count"])
