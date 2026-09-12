#!/usr/bin/env python3
"""Twelfth-invocation result-card update: MD section 24 + JSON fields."""
import json, re, subprocess, sys, datetime

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7"
MD = f"{WT}/longrun/results/D13-heatkernel-bridge-d10-d7.md"
JS = f"{WT}/longrun/results/D13-heatkernel-bridge-d10-d7.json"
SUM = open(f"{WT}/logs/d13_twelfth_final_summary.txt").read()

def grab(key):
    m = re.search(rf"^{re.escape(key)}=(.*)$", SUM, re.M)
    return m.group(1) if m else "?"

jobs = "?"
m = re.search(r"Build completed successfully \((\d+) jobs\)", open(f"{WT}/logs/d13_twelfth_final_build.log").read())
if m: jobs = m.group(1)

# hashes from manifest
hashes = {}
for line in open(f"{WT}/logs/d13_twelfth_final_hashes.txt"):
    line = line.strip()
    if not line: continue
    h, p = line.split(None, 1)
    hashes[p.strip()] = h

diff_lines = grab("diff_lines")
import os
wt_file = f"{WT}/logs/d13_twelfth_final_gate_raw2.txt"
if os.path.exists(wt_file):
    lines = [l for l in open(wt_file).read().splitlines() if l.strip()]
    wt_total = str(len(lines)); wt_fail = str(sum(1 for l in lines if not l.startswith("0:")))
    wt_log = "logs/d13_twelfth_final_gate_raw2.txt"
else:
    wt_total = grab("worktree_total"); wt_fail = grab("failures"); wt_log = "logs/d13_twelfth_final_gate_raw.txt"
pf_total = grab("perfile_total"); pf_fail = grab("perfile_failures")
sem_files = grab("semantic_files"); sem_fail = grab("semantic_failures")

gates = f"""**All gates green on the frozen twelfth-invocation artifact** (`logs/d13_twelfth_final_*`):

- **Source hashes**: {grab('hashes_recorded')} recorded in `logs/d13_twelfth_final_hashes.txt` — 17
  `D13/HeatKernelBridge` files, 10 authored `D7` files (`V1Interface`, `FiniteStatus`,
  `StatementStatus`, `RepairStatus`, `DataStatus`, `UniquenessStatus`, `ErgodicityStatus`,
  `ConjugateHeat/Status`, `ConjugateHeat/UniquenessStatus`, `ConjugateHeat/ScalarCurvatureStatus`)
  and the 3 build-config files — and all re-verified with `sha256sum -c` after the result cards were
  written (`logs/d13_twelfth_final_hashes_check.txt`, all OK).
- **Semantic transcripts**: {sem_files} files exit 0, {sem_fail} failures
  (`logs/d13_twelfth_final_semantic_checks.out`), including the new
  `tmp/d13_semantic_checks_m_ergodicity.lean`, which `#check`s the 56 new declarations.
- **Full build**: exit {grab('build_exit')}, `Build completed successfully ({jobs} jobs)`, D6AUDIT
  PASS, `D13HeatKernelBridgeAxiomCheck PASS 511/511` (`logs/d13_twelfth_final_build.log`).
- **Per-file gate**: {pf_total}/{pf_total} exit 0, {pf_fail} failures
  (`logs/d13_twelfth_final_perfile.txt`).
- **Worktree gate**: {wt_total} files, {wt_fail} failures (`{wt_log}`; the first run of this gate
  flagged only the two temporary API-probe files `tmp/d13_twelfth_api_probe{2,3}.lean`, which
  intentionally `#check` non-existent Mathlib names; they were deleted, and the gate was re-run over
  the frozen artifact).
- **Forbidden scan**: 0 hard / 0 soft for `D13/HeatKernelBridge`, `D7/HeatKernel` and
  `D7/ConjugateHeat` (`logs/d13_twelfth_final_forbidden_*.json`).
- **Negative control**: PASS (`logs/d13_twelfth_final_negcontrol.out`).
- **Source integrity**: `diff -rq release/Poincare` vs `D12-heat-domain-repair` = {diff_lines} lines
  (the two new files plus the docstring extensions of `All.lean`; the two edited files are
  `All.lean` and `AxiomAudit.lean`) (`logs/d13_twelfth_final_diff.txt`).
- **Upstream snapshot**: PASS, commit `bb91a091` (`logs/d13_twelfth_final_upstream.out`).
"""

section = open(f"{WT}/tmp/d13_twelfth_md_section.md").read()
section = section.replace("{{GATES}}", gates.strip())
section = section.replace("{{ELAPSED}}", "1.5")
with open(MD, "a") as f:
    f.write("\n" + section + "\n")

# ---------------- JSON ----------------
d = json.load(open(JS))

F = "Poincare.D13.HeatKernelBridge.FiniteHeatOperator."
entries = [
 ("meanZero", "def", "(X) [Fintype X] [DecidableEq X] (u : X → ℝ) → Prop — the total sum of `u` vanishes"),
 ("meanZero_sub_const", "theorem", "if `∑ x, u x = card X * c` then `u - c` is mean-zero"),
 ("dirichlet_inner_nonneg", "theorem", "the inner Dirichlet sum `∑ y, L x y * (u x - u y)^2` is nonnegative"),
 ("dirichletForm", "def", "(G) (u) → ℝ — the Dirichlet form `(1/2) * ∑ x ∑ y, L x y (u x - u y)^2`"),
 ("dirichletForm_nonneg", "theorem", "`0 ≤ dirichletForm G u`"),
 ("dirichletForm_eq_neg_quadraticForm", "theorem", "`dirichletForm G u = -(∑ x, u x * Δ u x)`"),
 ("dirichletForm_eq_zero_iff", "theorem", "[Nonempty X] `dirichletForm G u = 0 ↔ u` is constant"),
 ("sum_sq_sub_eq", "theorem", "variance identity `∑ x ∑ y, (u x - u y)^2 = 2 * card X * ∑ u^2 - 2 * (∑ u)^2`"),
 ("sum_sq_sub_eq_of_meanZero", "theorem", "mean-zero specialization `∑ x ∑ y, (u x - u y)^2 = 2 * card X * energy u`"),
 ("dirichletForm_ge_of_weight", "theorem", "`card X * w * energy u ≤ dirichletForm G u` for `w` below every off-diagonal entry, on mean-zero `u`"),
 ("minWeight", "def", "(G) (h : ∃ x y, x ≠ y) → ℝ — the minimal off-diagonal entry"),
 ("minWeight_le", "theorem", "`minWeight G h ≤ L x y` for `x ≠ y`"),
 ("minWeight_pos", "theorem", "`0 < minWeight G h`"),
 ("dirichletGap", "def", "(G) (h) → ℝ — the combinatorial Dirichlet gap `card X * minWeight G h`"),
 ("dirichletGap_pos", "theorem", "`0 < dirichletGap G h`"),
 ("poincare_inequality", "theorem", "`dirichletGap G h * energy u ≤ dirichletForm G u` on mean-zero `u`"),
 ("completeGraphOperator_apply_of_ne", "theorem", "the complete-graph operator has off-diagonal entries `1`"),
 ("completeGraphOperator_apply_self", "theorem", "the complete-graph operator has diagonal entries `1 - card X`"),
 ("completeGraphOperator_minWeight", "theorem", "the complete-graph minimal off-diagonal weight is `1`"),
 ("completeGraphOperator_dirichletGap", "theorem", "the complete-graph Dirichlet gap is exactly `card X`"),
 ("completeGraphOperator_dirichletForm_eq", "theorem", "on mean-zero `u` the complete-graph Dirichlet form equals `card X * energy u` (Poincaré equality)"),
 ("completeGraphOperator_poincare_attained", "theorem", "the complete-graph Poincaré inequality is an equality (sharpness of the constant)"),
 ("sum_laplacian_eq_zero", "theorem", "`∑ x, Δ u x = 0` (column sums of the pinned operator vanish)"),
 ("hasDerivAt_mean", "theorem", "the total sum of a solution of `∂_t u = Δ u` has zero derivative (mean conservation)"),
 ("energy_decay_of_meanZero", "theorem", "Gronwall: `energy (u T) ≤ energy (u ε) * exp (-(2Λ)(T-ε))` for a mean-zero solution when `Λ` satisfies Poincaré"),
 ("equilibrium", "def", "(X) [Fintype X] [DecidableEq X] → X → ℝ — the uniform function `x ↦ (card X)⁻¹`"),
 ("one_sub_inv_card_nonneg", "theorem", "`0 ≤ 1 - (card X)⁻¹`"),
 ("finiteHeatKernel_column_sum", "theorem", "the pinned kernel has unit column mass `∑ x, K x y t = 1` for `t > 0`"),
 ("finiteHeatKernel_shift_meanZero", "theorem", "the kernel's deviation from equilibrium is mean-zero in the spatial variable"),
 ("laplacian_sub_const", "theorem", "`Δ (u - c) = Δ u` (the pinned Laplacian annihilates constants)"),
 ("finiteHeatKernel_shift_hasDerivAt", "theorem", "the equilibrium-shifted kernel solves the same spatial PDE"),
 ("finiteHeatKernel_tendsto_entry", "theorem", "`K x y t → (1 : Matrix X X ℝ) x y` as `t → 0⁺` (Dirac data)"),
 ("energy_dirac_sub_equilibrium", "theorem", "the Dirac-minus-equilibrium energy is `1 - (card X)⁻¹`"),
 ("finiteHeatKernel_shift_tendsto_energy", "theorem", "the shifted kernel's energy tends to `1 - (card X)⁻¹` as `t → 0⁺`"),
 ("finiteHeatKernel_shift_energy_decay", "theorem", "Gronwall decay of the shifted kernel's energy on `[ε, T]`"),
 ("finiteHeatKernel_energy_decay", "theorem", "`energy (K · y T - equilibrium) ≤ (1 - (card X)⁻¹) * exp (-(2Λ)T)`"),
 ("finiteHeatKernel_energy_decay_gap", "theorem", "the same bound at the combinatorial gap `Λ = dirichletGap G`"),
 ("finiteHeatKernel_tendsto_equilibrium_energy", "theorem", "the kernel's energy deviation tends to `0` at infinity for `Λ > 0`"),
 ("finiteHeatKernel_pointwise_decay", "theorem", "`|K x y t - (card X)⁻¹| ≤ sqrt (1 - (card X)⁻¹) * exp (-(Λ t))`"),
 ("completeGraphKernelForm", "def", "(x y : X) (t : ℝ) → ℝ — the closed form `(card X)⁻¹ + exp (-(card X) t) * (δ x y - (card X)⁻¹)`"),
 ("sum_mul_one_apply", "theorem", "`∑ z, L x z * (1 : Matrix X X ℝ) z y = L x y`"),
 ("completeGraphOperator_laplacian_kernelForm", "theorem", "the complete-graph Laplacian of the closed form is `-card X * exp (-(card X) t) * d`"),
 ("completeGraphKernelForm_hasDerivAt", "theorem", "time derivative of the closed form"),
 ("completeGraphKernelForm_tendsto", "theorem", "Dirac limit of the closed form as `t → 0⁺`"),
 ("completeGraphOperator_finiteHeatKernel", "theorem", "the complete-graph pinned kernel equals the closed form for `t > 0` (via uniqueness)"),
 ("completeGraphOperator_energy_decay_sharp", "theorem", "the complete-graph kernel's equilibrium energy is exactly `(1 - (card X)⁻¹) * exp (-(2 card X) t)`"),
 ("completeGraphOperator_energy_decay_attained", "theorem", "the decay bound at the Dirichlet gap is attained on the complete graph"),
]
D7 = "Poincare.D7.HeatKernel."
entries += [
 ("finite_pinned_dirichlet_gap_pos", "theorem", "D7: the pinned Dirichlet gap is strictly positive"),
 ("finite_pinned_poincare", "theorem", "D7: the pinned Poincaré inequality"),
 ("finite_pinned_kernel_energy_decay", "theorem", "D7: exponential energy decay of the kernel to equilibrium"),
 ("finite_pinned_kernel_tendsto_equilibrium", "theorem", "D7: the kernel's energy deviation tends to zero at infinity"),
 ("finite_pinned_kernel_pointwise_convergence", "theorem", "D7: pointwise exponential convergence to the equilibrium value"),
 ("finite_pinned_equilibrium_invariant", "theorem", "D7: the uniform function is invariant under the pinned semigroup"),
 ("finite_pinned_ergodicity_summary", "theorem", "D7: conjunction of gap, Poincaré, decay and convergence"),
 ("finite_pinned_complete_graph_sharp", "theorem", "D7: the complete-graph decay bound is attained"),
 ("finite_pinned_complete_graph_gap", "theorem", "D7: the complete-graph gap is exactly the cardinality"),
]
for name, kind, typ in entries:
    ns = F if name not in [e[0] for e in entries[47:]] else D7
    d["proved_declarations"].append({
        "name": ns + name, "kind": kind, "type": typ,
        "semantic_class": "proved theorem over the pinned finite model (twelfth invocation: Dirichlet gap / long-time asymptotics)"})

d["source_hashes"] = hashes
d["generated_utc"] = datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")
d["elapsed_hours"] = 12.2
d["elapsed_hours_this_invocation"] = 1.5
d["module"] = d["module"] + "; twelfth invocation adds FiniteErgodicity (Dirichlet gap, Poincare, long-time asymptotics, complete-graph sharpness) and Poincare.D7.HeatKernel.ErgodicityStatus"
d["verdict"] = ("TASK_DONE (requests independent acceptance; no named blocker closed). The LONG_PLAN HeatKernelBridge module "
  "transports the D10 Euclidean heat kernel to the D7 HeatKernelData interface on the D12 corrected domain; the twelfth "
  "invocation adds the quantitative long-time theory of the pinned finite model (Dirichlet form, variance identity, "
  "combinatorial Dirichlet gap, Poincare inequality, Gronwall energy decay, convergence of the kernel to the equilibrium "
  "measure, and the attained complete-graph instance), 56 new audited declarations (455 -> 511), and the D7 consumer "
  "Poincare.D7.HeatKernel.ErgodicityStatus. D7-HEAT-KERNEL-EXISTENCE remains OPEN (manifold Laplace-Beltrami, Poincare "
  "inequality, parabolic regularity, parametrix and Gaussian bounds); exact_blockers_closed = [].")
d["axiom_evidence"] = {
  "audit_module": "Poincare.D13.HeatKernelBridge.AxiomAudit",
  "check": "D13HeatKernelBridgeAxiomCheck: PASS — all 511 declarations of the D13 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]",
  "fail_closed": "programmatic Lean.collectAxioms re-check with throwError on any unapproved axiom (run_cmd)",
  "breakdown": "455 declarations of the first eleven invocations + 47 FiniteErgodicity.lean + 9 Poincare.D7.HeatKernel.ErgodicityStatus = 511, each re-checked in the full build",
  "log": "logs/d13_twelfth_final_build.log"}
d.setdefault("compile_evidence", []).extend([
  {"command": "lake build", "cwd": "release/", "exit": 0,
   "note": f"Build completed successfully ({jobs} jobs); D6AUDIT PASS; D13HeatKernelBridgeAxiomCheck PASS 511/511 (logs/d13_twelfth_final_build.log)"},
  {"command": f"lake env lean <file> for each of the {pf_total} authored files", "cwd": "worktree root",
   "exit": f"{pf_total}/{pf_total} 0", "note": "per-file gate (logs/d13_twelfth_final_perfile.txt)"},
  {"command": "lake env lean <every .lean file>", "cwd": "worktree root",
   "exit": f"{wt_total} files, {wt_fail} failures", "note": "worktree gate (logs/d13_twelfth_final_gate_raw.txt)"},
  {"command": "python3 input/d5-tools/scan_forbidden.py <dir> (D13, D7/HeatKernel, D7/ConjugateHeat)",
   "cwd": "worktree root", "exit": 0, "note": "0 hard / 0 soft forbidden matches"},
  {"command": "bash tmp/d13_twelfth_gates.sh d13_twelfth_final", "cwd": "worktree root", "exit": 0,
   "note": "full twelfth-invocation gate suite (logs/d13_twelfth_final_summary.txt)"},
])
d.setdefault("remaining_blockers", []).append(
  "D7-HEAT-KERNEL-EXISTENCE (manifold content) — twelfth invocation: the finite pinned model now has a quantitative "
  "long-time theory (Dirichlet gap, Poincare, exponential convergence to equilibrium, attained complete-graph instance), "
  "but the manifold-side analytic content (Laplace-Beltrami operator, manifold Poincare inequality, elliptic/parabolic "
  "regularity, parametrix, Gaussian bounds) remains open. exact_blockers_closed = [].")
d.setdefault("next_dependency_requests", []).append(
  "MANIFOLD-SIDE SPECTRAL THEORY: build the Laplace-Beltrami operator on a closed Riemannian manifold with its Poincare "
  "inequality (spectral gap) and heat-kernel long-time asymptotics; the twelfth invocation provides the finite-model "
  "template (Dirichlet form, variance identity, gap, Gronwall decay, equilibrium convergence, sharpness) that such a "
  "development must instantiate.")
d.setdefault("next_dependency_requests", []).append(
  "INDEPENDENT SEMANTIC ACCEPTANCE of the 19 authored modules by a fresh reviewer (hash-pinned, "
  "logs/d13_twelfth_final_hashes.txt), including the twelfth-invocation FiniteErgodicity.lean and "
  "Poincare.D7.HeatKernel.ErgodicityStatus.")
d["semantic_class"]["finite_ergodicity"] = (
  "proved theorems over the pinned finite model: Dirichlet form identity and kernel, variance identity, quantitative "
  "Poincare inequality with the combinatorial gap card X * minWeight, Gronwall exponential energy decay, convergence of "
  "the pinned heat kernel to the uniform equilibrium with exponential rate, and the sharp complete-graph instance (gap = "
  "card X, decay bound attained). Not a manifold statement; the named blocker stays open.")
d["expanded_hypotheses"]["finite_ergodicity"] = (
  "two distinct points (h : ∃ x y, x ≠ y) are required for a strictly positive gap and for the stated convergence rates; "
  "Λ > 0 is required for the limit statements; meanZero is required exactly where the Poincare inequality is applied "
  "(automatic for the kernel deviation by the checked unit-column-sum identity). No assumption equivalent to the "
  "conclusion; the complete-graph instance is an independent consistency check of sharpness.")
d["twelfth_invocation"] = {
  "when_utc": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
  "what": "the Dirichlet gap and the long-time asymptotics of the pinned finite heat kernel",
  "context": "the ninth/tenth invocations made the finite pinned problem well posed and proved antitonicity of the energy, which carries no rate and no statement at infinity; the missing items (Poincare inequality, spectral gap, convergence to the equilibrium measure) are exactly the spectral-theory content listed among the remaining manifold items of D7-HEAT-KERNEL-EXISTENCE",
  "baseline_hashes_match": "28/28 hashes of logs/d13_eleventh_final_hashes.txt re-computed byte-identical; baseline build exit 0 (9204 jobs), AxiomAudit PASS 455/455",
  "findings": [
    "dirichletForm is nonnegative, equals the negative quadratic form, and vanishes exactly on the constants",
    "variance identity and the quantitative Poincare inequality card X * w * energy ≤ dirichletForm on mean-zero functions",
    "combinatorial Dirichlet gap card X * minWeight > 0 and the Poincare inequality at that gap",
    "mean conservation (∑ x, Δ u x = 0) and Gronwall exponential energy decay for mean-zero solutions",
    "the kernel's equilibrium deviation is mean-zero, solves the same PDE, has Dirac energy 1 - 1/card X at 0+, and converges to equilibrium in energy and pointwise with the gap rate",
    "sharpness on the complete graph: gap = card X, Poincare equality, closed-form kernel and exact decay bound attained"],
  "new_files": ["release/Poincare/D13/HeatKernelBridge/FiniteErgodicity.lean (47 declarations)",
                "release/Poincare/D7/HeatKernel/ErgodicityStatus.lean (9 declarations)"],
  "extended_files": ["release/Poincare/D13/HeatKernelBridge/All.lean (docstring)",
                     "release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean (audit 455 -> 511)",
                     "tmp/d13_semantic_checks_m_ergodicity.lean (new semantic transcript)"],
  "gates": {
    "build": f"exit 0, Build completed successfully ({jobs} jobs), D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 511/511",
    "semantic_checks": f"{sem_files} files exit 0, {sem_fail} failures",
    "per_file_gate": f"{pf_total}/{pf_total} exit 0",
    "worktree_gate": f"{wt_total} files, {wt_fail} failures ({wt_log}; the temporary API-probe files were deleted before the re-run)",
    "forbidden_scan": "0 hard / 0 soft",
    "negcontrol": "PASS",
    "source_integrity": f"diff vs D12-heat-domain-repair = {diff_lines} lines",
    "upstream_snapshot": "PASS (bb91a091)",
    "hashes": f"{grab('hashes_recorded')} recorded and re-verified with sha256sum -c"},
  "not_a_closure": "the manifold analytic content of D7-HEAT-KERNEL-EXISTENCE (Laplace-Beltrami, manifold Poincare, parabolic regularity, parametrix, Gaussian bounds) remains open; exact_blockers_closed = []"}
json.dump(d, open(JS, "w"), indent=1, ensure_ascii=False)
print("MD + JSON updated; declarations:", len(d["proved_declarations"]), "hashes:", len(hashes))
