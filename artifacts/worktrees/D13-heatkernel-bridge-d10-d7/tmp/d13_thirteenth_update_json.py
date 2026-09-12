import json, os, datetime

root = '/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7'
os.chdir(root)
P = 'longrun/results/D13-heatkernel-bridge-d10-d7.json'
d = json.load(open(P))

def read_counts(path):
    ok = fail = 0
    for line in open(path):
        line = line.strip()
        if not line or line in ('DONE', 'ALLDONE'):
            continue
        if line.split(':', 1)[0] == '0':
            ok += 1
        else:
            fail += 1
    return ok, fail

per_ok, per_fail = read_counts('logs/d13_thirteenth_final_perfile.txt')
wt_ok, wt_fail = read_counts('logs/d13_thirteenth_final_gate_raw.txt')
sem_lines = [l for l in open('logs/d13_thirteenth_final_semantic_all.out').read().splitlines()
             if l.strip() and l.strip() != 'ALLDONE']
sem_fail = sum(1 for l in sem_lines if not l.startswith('0:'))
hashes = [l.split()[1] for l in open('logs/d13_thirteenth_final_hashes.txt') if l.strip()]
assert not sem_fail and not per_fail and not wt_fail, (sem_fail, per_fail, wt_fail)

now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')

# ---- new declarations ----------------------------------------------------
new_decls = []
def add(name, kind, typ):
    new_decls.append({"name": name, "kind": kind, "type": typ,
        "semantic_class": "proved theorem (thirteenth invocation: weak heat equation on the corrected admissible-test-function domain)"})

D13 = "Poincare.D13.HeatKernelBridge."
add(D13+"IsWeakHeatKernelPDE.v1", "def", "D13: version tag of the weak heat-equation predicate")
add(D13+"IsWeakHeatKernelPDE", "structure", "D13: the weak (test-paired) heat equation over an admissible test class")
add(D13+"WeakHeatCertificates", "structure", "D13: the four analytic certificates (snapshot measurability/integrability, paired-Laplacian measurability, local uniform bound)")
add(D13+"weakHeatKernelPDE_of_hasDerivAt", "theorem", "D13: pointwise PDE + certificates => weak equation (mathlib dominated differentiation)")
add(D13+"IsHeatKernelPDE.toWeak", "theorem", "D13: the PDE-repaired predicate implies the weak equation")
add(D13+"IsWeakHeatKernelPDE.hasDerivAt", "theorem", "D13: restatement of the weak field")
add(D13+"IsWeakHeatKernelPDE.mono_class", "theorem", "D13: the weak equation restricts to admissible subclasses")
add(D13+"rpow_neg_half_le_of_le", "theorem", "D13: Gaussian prefactor monotonicity (4*pi*t)^(-n/2) <= (4*pi*a)^(-n/2) for 0 < a <= t")
add(D13+"mul_exp_neg_le_inv_e", "theorem", "D13: elementary maximum u*exp(-u) <= exp(-1) on u >= 0")
add(D13+"gaussianKernel_le_prefactor", "theorem", "D13: Gaussian sup bound K <= (4*pi*t)^(-n/2)")
add(D13+"gaussianKernel_abs_le_prefactor", "theorem", "D13: absolute-value Gaussian sup bound")
add(D13+"flatKernel_abs_le_prefactor", "theorem", "D13: bridge kernel sup bound at positive times")
add(D13+"flatLaplacianBound", "def", "D13: explicit uniform Laplacian bound (4*pi*a)^(-n/2)*(1/(e*a)+n/(2*a))")
add(D13+"flatHeatSpacetime_laplacian_apply", "theorem", "D13: explicit formula for the flat Laplacian of the bridge kernel")
add(D13+"flatKernel_continuous_snapshot", "theorem", "D13: continuity in the space variable of the flat kernel snapshot")
add(D13+"flatKernel_laplacian_continuous_snapshot", "theorem", "D13: continuity in the space variable of the flat Laplacian snapshot")
add(D13+"gaussianKernel_mul_sq_div_le", "theorem", "D13: first Laplacian term bound K*||z||^2/(4t^2) <= (4*pi*t)^(-n/2)/(e*t)")
add(D13+"flatKernel_laplacian_abs_le", "theorem", "D13: uniform bound |Delta K| <= flatLaplacianBound n a on [a,b], a>0")
add(D13+"flatWeakHeatCertificates_of_subclass", "theorem", "D13: the four certificates for the flat kernel on every subclass of the integrable class")
add(D13+"flatWeakHeatCertificates_integrable", "theorem", "D13: flat certificates on the continuous-integrable class")
add(D13+"flatWeakHeatCertificates_cc", "theorem", "D13: flat certificates on the C_c class")
add(D13+"flat_weakHeatKernel_integrable", "theorem", "D13: the D10 kernel satisfies the weak equation in every dimension (integrable class)")
add(D13+"flat_weakHeatKernel_cc", "theorem", "D13: the D10 kernel satisfies the weak equation in every dimension (C_c class)")
add(D13+"flat_weakHeatKernel_of_subclass", "theorem", "D13: the flat weak equation on every admissible subclass")
add(D13+"flat_weak_snapshot_refuted", "theorem", "D13: in positive dimension the flat kernel satisfies the weak equation while IsHeatKernelV1 is refuted")
add(D13+"finiteLaplacianBound", "def", "D13 finite model: total matrix mass bound sum x sum z |L x z|")
add(D13+"finiteLaplacianBound_nonneg", "theorem", "D13 finite model: the bound is nonnegative")
add(D13+"finiteHeatKernel_abs_le_one", "theorem", "D13 finite model: every pinned-kernel entry is in [0,1] at positive times")
add(D13+"finiteHeatKernel_laplacian_abs_le", "theorem", "D13 finite model: |Delta K| <= finiteLaplacianBound on [a,b], a>0")
add(D13+"finiteWeakHeatCertificates", "theorem", "D13 finite model: the four certificates (finite-type measurability/integrability, row-mass bound)")
add(D13+"finite_weakHeatKernel", "theorem", "D13 finite model: the pinned kernel satisfies the weak equation on the corrected domain")
add(D13+"finite_weak_and_pde_inhabited", "theorem", "D13 finite model: weak and pointwise predicates simultaneously inhabited")

D7 = "Poincare.D7.HeatKernel."
add(D7+"HeatKernelData.toHeatSpacetime", "def", "D7: the schematic spacetime attached to a legacy heat-kernel datum")
add(D7+"HeatKernelData.toHeatSpacetime_volume", "theorem", "D7: field lemma")
add(D7+"HeatKernelData.toHeatSpacetime_laplacian", "theorem", "D7: field lemma")
add(D7+"HeatKernelData.toHeatSpacetime_timeDerivative", "theorem", "D7: field lemma (timeDerivative := 0)")
add(D7+"HeatKernelData.toHeatSpacetime_dist", "theorem", "D7: field lemma")
add(D7+"HeatKernelData.toHeatSpacetime_dim", "theorem", "D7: field lemma")
add(D7+"heatKernelData_weakHeatEquation", "theorem", "D7: every legacy D7 heat-kernel datum satisfies the weak heat equation on the corrected domain")
add(D7+"heatKernelDataV1_weakHeatEquation", "theorem", "D7: the corrected-domain bridge datum satisfies the weak heat equation")
add(D7+"flat_weakHeatEquation_integrable", "theorem", "D7-level re-export of the flat weak equation (integrable class)")
add(D7+"flat_weakHeatEquation_cc", "theorem", "D7-level re-export of the flat weak equation (C_c class)")
add(D7+"flat_weak_and_snapshot_refuted", "theorem", "D7-level: weak equation holds while the snapshot predicate is refuted (positive dimension)")
add(D7+"finite_weakHeatEquation", "theorem", "D7-level: the pinned finite model satisfies the weak equation")
add(D7+"weak_status_summary", "theorem", "D7-level summary of the weak-equation bridge")

assert len(new_decls) == 45, len(new_decls)
d['proved_declarations'].extend(new_decls)

# ---- top-level updates ---------------------------------------------------
d['generated_utc'] = now
d['axiom_evidence']['check'] = ("D13HeatKernelBridgeAxiomCheck: PASS — all 556 declarations of the "
    "D13 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]")
d['axiom_evidence']['breakdown'] = ("511 declarations of the first twelve invocations + 25 WeakHeatEquation.lean + 7 WeakFinite.lean + "
    "13 Poincare.D7.HeatKernel.WeakStatus = 556, each re-checked in the full build")
d['axiom_evidence']['log'] = 'logs/d13_thirteenth_final_build.log'
d['semantic_class']['weak_heat_equation'] = ("WeakHeatEquation.lean (thirteenth invocation, 25 declarations): the versioned weak "
    "(test-paired) predicate IsWeakHeatKernelPDE, the analytic certificates WeakHeatCertificates, the proved transfer from the "
    "pointwise PDE by mathlib's dominated differentiation, the explicit Gaussian/Laplacian bounds for the D10 kernel "
    "(including the uniform bound |Delta K| <= (4*pi*a)^(-n/2)(1/(e a)+n/(2 a)) on [a,b], a>0), the flat weak instances in "
    "every dimension on both standard classes, and the contrast with the refuted snapshot predicate. Conditional interface "
    "for a general datum (the certificates are explicit hypotheses); proved theorem for the flat D10 model.")
d['semantic_class']['weak_finite'] = ("WeakFinite.lean (thirteenth invocation, 7 declarations): the same weak interface on the pinned "
    "finite Markov-chain model, with a finite-dimensional certificate proof (entries in [0,1]; |Delta K| <= sum x sum z |L x z|; "
    "measurability/integrability from Integrable.of_finite) and the simultaneous inhabitation of the weak and pointwise predicates.")
d['semantic_class']['d7_weak_status'] = ("Poincare.D7.HeatKernel.WeakStatus (thirteenth invocation, 13 declarations): the D7-level legacy "
    "transport (every legacy D7 HeatKernelData satisfies the weak equation from its heatEquation field, given the certificates), the "
    "V1 transport, the flat re-exports, the pinned finite instance and the status summary.")
d['expanded_hypotheses']['weak_heat_certificates'] = ("WeakHeatCertificates S C K: snapshot_measurable / snapshot_integrable "
    "(the kernel snapshot against an admissible test function is ae-measurable and integrable), laplacian_measurable (the paired "
    "Laplacian snapshot is ae-measurable), laplacian_locally_bounded (on every [a,b] with a>0 the paired Laplacian is uniformly "
    "bounded in space and time). These are exactly the hypotheses of mathlib's dominated-differentiation theorem. They are PROVED "
    "for the D10 Euclidean kernel (flatWeakHeatCertificates_of_subclass and its instances) and for the pinned finite kernel "
    "(finiteWeakHeatCertificates); for a general manifold datum they are the missing analytic input (Gaussian bounds for Delta K), "
    "not axioms.")
d['next_dependency_requests'].append("INDEPENDENT SEMANTIC ACCEPTANCE of the 22 authored modules by a fresh reviewer "
    "(hash-pinned, logs/d13_thirteenth_final_hashes.txt), including the thirteenth-invocation WeakHeatEquation.lean, WeakFinite.lean "
    "and Poincare.D7.HeatKernel.WeakStatus.")
d['next_dependency_requests'].append("MANIFOLD-SIDE CERTIFICATES: to use the weak equation on a closed Riemannian manifold, supply "
    "WeakHeatCertificates for the Laplace-Beltrami heat kernel: measurability/integrability of the kernel snapshots and the local "
    "uniform bound on Delta K (the Gaussian upper bound for the second derivatives). The transfer weakHeatKernelPDE_of_hasDerivAt "
    "then applies verbatim; no re-proof of the weak formulation is needed.")

remaining = d['remaining_blockers']
for i, r in enumerate(remaining):
    if r.startswith('D7-HEAT-KERNEL-EXISTENCE'):
        remaining[i] = ("D7-HEAT-KERNEL-EXISTENCE (manifold content) — thirteenth invocation: the weak (test-paired) form of the "
            "heat equation now exists on the corrected admissible-test-function domain, the transfer from the pointwise PDE is proved "
            "by mathlib dominated differentiation, and the certificates needed to run it are identified and PROVED for two models "
            "(the D10 flat kernel with the uniform bound |Delta K| <= (4*pi*a)^(-n/2)(1/(e a)+n/(2 a)) on [a,b], a>0, and the pinned "
            "finite Markov-chain kernel with the matrix-mass bound). The manifold content (Laplace-Beltrami operator, manifold "
            "Poincare inequality, parabolic regularity, parametrix, Gaussian bounds) remains open and the named blocker is NOT closed.")
        break

d['thirteenth_invocation'] = {
 "when_utc": now,
 "what": "the weak (test-paired) heat equation on the corrected admissible-test-function domain, with flat and pinned-finite model instances",
 "context": ("the D7 interfaces (and the D13 repair IsHeatKernelPDE) state the heat equation pointwise at each space point; downstream "
    "semigroup/PDE arguments consume it paired against test functions. The passage to the weak form is not formal: it needs snapshot "
    "measurability/integrability, paired-Laplacian measurability and a local uniform bound on Delta K — on a manifold exactly the "
    "Gaussian bounds listed among the missing inputs of D7-HEAT-KERNEL-EXISTENCE."),
 "baseline_hashes_match": "30/30 hashes of logs/d13_twelfth_final_hashes.txt re-computed byte-identical; baseline build exit 0 (9206 jobs, D6AUDIT PASS)",
 "findings": [
  "IsWeakHeatKernelPDE (v1): the weak equation d/dt ∫ phi K(.,y,t) = ∫ phi Delta K(.,y,t) over the D12 admissible test class",
  "WeakHeatCertificates: the four analytic certificates, exactly the hypotheses of mathlib's parametric-integral theorem",
  "weakHeatKernelPDE_of_hasDerivAt: pointwise PDE + certificates => weak equation, proved by hasDerivAt_integral_of_dominated_loc_of_deriv_le",
  "the certificates are PROVED for the explicit D10 kernel: Gaussian sup bound, u exp(-u) <= 1/e, and the uniform Laplacian bound (4*pi*a)^(-n/2)(1/(e a)+n/(2 a)) on [a,b], a>0",
  "flat_weakHeatKernel_integrable / _cc: the D10 kernel satisfies the weak equation in every dimension on both standard classes",
  "the certificates are also PROVED for the pinned finite kernel (WeakFinite.lean): entries in [0,1], |Delta K| <= sum x sum z |L x z|, finite-type measurability/integrability; a structurally different certificate proof",
  "flat_weak_snapshot_refuted: in positive dimension the weak equation holds while the legacy snapshot predicate IsHeatKernelV1 is refuted",
  "D7-level: every legacy HeatKernelData satisfies the weak equation from its heatEquation field (heatKernelData_weakHeatEquation), and so does the pinned finite model (finite_weakHeatEquation)"
 ],
 "new_files": [
  "release/Poincare/D13/HeatKernelBridge/WeakHeatEquation.lean (25 declarations)",
  "release/Poincare/D13/HeatKernelBridge/WeakFinite.lean (7 declarations)",
  "release/Poincare/D7/HeatKernel/WeakStatus.lean (13 declarations)"
 ],
 "extended_files": [
  "release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean (imports, 45 #print lines, 45 names; audit 511 -> 556)",
  "tmp/d13_semantic_checks_n_weak.lean (new extended semantic transcript)"
 ],
 "gates": {
  "build": "exit 0, Build completed successfully (9209 jobs), D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 556/556",
  "semantic_checks": f"{len(sem_lines)} files exit 0, {sem_fail} failures",
  "per_file_gate": f"{per_ok}/{per_ok+per_fail} exit 0",
  "worktree_gate": f"{wt_ok} files, {wt_fail} failures (logs/d13_thirteenth_final_gate_raw.txt)",
  "forbidden_scan": "0 hard / 0 soft (D13/HeatKernelBridge, D7/HeatKernel)",
  "negcontrol": "PASS",
  "source_integrity": "diff vs D12-heat-domain-repair = 12 'Only in' lines: the new D13 tree plus the 11 authored D7 consumer files (including WeakStatus.lean); no D12 file modified",
  "upstream_snapshot": "PASS (bb91a091)",
  "hashes": f"{len(hashes)} recorded and re-verified with sha256sum -c"
 },
 "not_a_closure": ("the weak equation is a weakening of the pointwise PDE (the converse is not claimed and is false without further "
    "regularity); the manifold content of D7-HEAT-KERNEL-EXISTENCE remains open; exact_blockers_closed = []")
}

d['source_hashes'] = {}
for line in open('logs/d13_thirteenth_final_hashes.txt'):
    digest, path = line.split()
    d['source_hashes'][path] = digest

d['compile_evidence'].append({"command": "bash tmp/d13_thirteenth_final_quick_gates.sh && (worktree gate)",
    "cwd": "worktree root",
    "exit": 0, "note": "full thirteenth-invocation final gate suite (logs/d13_thirteenth_final_*)"})
d['compile_evidence'].append({"command": "cd release && lake env lean Poincare/D13/HeatKernelBridge/WeakHeatEquation.lean",
    "cwd": "release", "exit": 0, "note": "new D13 weak-equation module (25 declarations)"})
d['compile_evidence'].append({"command": "cd release && lake env lean Poincare/D13/HeatKernelBridge/WeakFinite.lean",
    "cwd": "release", "exit": 0, "note": "new D13 finite-model weak-equation module (7 declarations)"})
d['compile_evidence'].append({"command": "cd release && lake env lean Poincare/D7/HeatKernel/WeakStatus.lean",
    "cwd": "release", "exit": 0, "note": "new D7 consumer module (13 declarations)"})
d['compile_evidence'].append({"command": "cd release && lake env lean Poincare/D13/HeatKernelBridge/AxiomAudit.lean",
    "cwd": "release", "exit": 0, "note": "D13HeatKernelBridgeAxiomCheck PASS 556/556"})

elapsed = float(os.environ.get('D13_ELAPSED', '1.4'))
d['elapsed_hours_this_invocation'] = round(elapsed, 2)
d['elapsed_hours'] = round(11.7 + elapsed, 2)
d['verdict'] = ("TASK_DONE (requests independent acceptance; no named blocker closed). The thirteenth invocation adds the weak "
    "(test-paired) heat equation on the D12 corrected admissible-test-function domain: the versioned predicate "
    "IsWeakHeatKernelPDE, the explicit analytic certificates, the proved transfer from the pointwise PDE by mathlib dominated "
    "differentiation, the proved Gaussian/Laplacian bounds and the resulting flat D10 instances in every dimension on both "
    "standard classes, the same weak equation for the pinned finite model with a finite-dimensional certificate proof, and the "
    "D7-level legacy and finite transports. 45 new audited declarations (511 -> 556). D7-HEAT-KERNEL-EXISTENCE (manifold content) "
    "remains open and exact_blockers_closed = [].")

json.dump(d, open(P, 'w'), indent=1, ensure_ascii=False)
print('json updated; proved_declarations =', len(d['proved_declarations']),
      '; hashes =', len(d['source_hashes']),
      '; perfile', per_ok, per_fail, '; worktree', wt_ok, wt_fail, '; semantic', len(sem_lines), sem_fail)
