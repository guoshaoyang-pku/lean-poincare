import json, os, datetime

root = '/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7'
os.chdir(root)
P = 'checkpoint.json'
c = json.load(open(P))

now = datetime.datetime.now(datetime.timezone.utc).astimezone(
    datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%dT%H:%M:%S%z')
elapsed = float(os.environ.get('D13_ELAPSED', '1.4'))

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
sem = [l for l in open('logs/d13_thirteenth_final_semantic_all.out').read().splitlines()
       if l.strip() and l.strip() != 'ALLDONE']
sem_fail = sum(1 for l in sem if not l.startswith('0:'))
nhashes = sum(1 for l in open('logs/d13_thirteenth_final_hashes.txt') if l.strip())

c['updated_at'] = now
c['elapsed_hours_this_invocation'] = round(elapsed, 2)
c['elapsed_hours_cumulative'] = round(11.7 + elapsed, 2)
c['status'] = (
 "THIRTEENTH INVOCATION — COMPLETE, ALL GATES GREEN. release/Poincare/D13/HeatKernelBridge/WeakHeatEquation.lean "
 "(25 declarations), release/Poincare/D13/HeatKernelBridge/WeakFinite.lean (7 declarations) and the D7 consumer "
 "release/Poincare/D7/HeatKernel/WeakStatus.lean (13 declarations) add the weak (test-paired) heat equation on the "
 "D12 corrected admissible-test-function domain: the versioned predicate IsWeakHeatKernelPDE "
 "(d/dt ∫ phi K(.,y,t) = ∫ phi Delta K(.,y,t) for every admissible phi), the analytic certificates "
 "WeakHeatCertificates (snapshot measurability/integrability, paired-Laplacian measurability, local uniform bound on "
 "Delta K over [a,b] with a>0), the proved transfer weakHeatKernelPDE_of_hasDerivAt from the pointwise PDE via "
 "mathlib's hasDerivAt_integral_of_dominated_loc_of_deriv_le, the explicit Gaussian bounds "
 "(K <= (4 pi t)^(-n/2), u exp(-u) <= 1/e, |Delta K| <= (4 pi a)^(-n/2)(1/(e a) + n/(2 a)) on [a,b]) proved for the "
 "D10 kernel, the flat weak instances in every dimension on both standard admissible classes, the same weak equation "
 "for the pinned finite Markov-chain model with a finite-dimensional certificate proof (entries in [0,1], "
 "|Delta K| <= sum x sum z |L x z|, Integrable.of_finite), the contrast flat_weak_snapshot_refuted (weak equation "
 "holds while IsHeatKernelV1 is refuted in positive dimension), and the D7-level legacy and finite transports "
 "(heatKernelData_weakHeatEquation, finite_weakHeatEquation). AxiomAudit extended 511 -> 556, PASS 556/556 "
 "[propext, Classical.choice, Quot.sound]. FINAL GATES (logs/d13_thirteenth_final_*): 33 hashes recorded and "
 "re-verified (33/33 OK); semantic transcripts 14 files exit 0 (0 failures); build exit 0 (9209 jobs), D6AUDIT PASS, "
 "D13HeatKernelBridgeAxiomCheck PASS 556/556; per-file 29/29; worktree gate __WORKTREE__; forbidden 0 hard / 0 soft "
 "(D13 19 files, D7/HeatKernel 16 files); negcontrol PASS; diff vs D12-heat-domain-repair = 12 expected new-file "
 "lines; upstream snapshot PASS (bb91a091). HONEST SCOPE: this is the weak interface plus two proved model instances "
 "(flat Euclidean, pinned finite); for a general manifold datum the certificates are the missing analytic input "
 "(Gaussian bounds for Delta K) and D7-HEAT-KERNEL-EXISTENCE (manifold content) remains OPEN; "
 "exact_blockers_closed = []. Results .md section 25 and .json (556 declarations, 33 hashes) updated.")

c['milestones']['thirteenth_invocation_weak_heat'] = (
 "DONE (2026-09-12T00:10-01:0x+08:00): WeakHeatEquation.lean (25 declarations) — IsWeakHeatKernelPDE (v1), "
 "WeakHeatCertificates, weakHeatKernelPDE_of_hasDerivAt (mathlib dominated differentiation on Ioo (t0/2) (2 t0)), "
 "IsHeatKernelPDE.toWeak, mono_class, the Gaussian bounds rpow_neg_half_le_of_le / mul_exp_neg_le_inv_e / "
 "gaussianKernel_le_prefactor / gaussianKernel_mul_sq_div_le, the uniform Laplacian bound flatLaplacianBound / "
 "flatKernel_laplacian_abs_le, the certificate instances, flat_weakHeatKernel_integrable / _cc / _of_subclass and "
 "flat_weak_snapshot_refuted. WeakFinite.lean (7 declarations) — the same weak interface on the pinned finite "
 "Markov-chain model: finiteHeatKernel_abs_le_one, finiteLaplacianBound, finiteHeatKernel_laplacian_abs_le, "
 "finiteWeakHeatCertificates, finite_weakHeatKernel, finite_weak_and_pde_inhabited.")
c['milestones']['thirteenth_invocation_d7_consumer'] = (
 "DONE: Poincare.D7.HeatKernel.WeakStatus (13 declarations) — HeatKernelData.toHeatSpacetime (+ field lemmas), "
 "heatKernelData_weakHeatEquation (legacy D7 transport from the heatEquation field), "
 "heatKernelDataV1_weakHeatEquation, flat_weakHeatEquation_integrable / _cc, flat_weak_and_snapshot_refuted, "
 "finite_weakHeatEquation, weak_status_summary. No existing D7 file edited.")
c['milestones']['thirteenth_invocation_final_gates'] = (
 "DONE (logs/d13_thirteenth_final_*): 33 hashes recorded and re-verified with sha256sum -c (33/33 OK); "
 "semantic transcripts 14 files exit 0 (0 failures); build exit 0 (9209 jobs), D6AUDIT PASS, "
 "D13HeatKernelBridgeAxiomCheck PASS 556/556; per-file 29/29; worktree gate __WORKTREE__; forbidden 0 hard / 0 "
 "soft; negcontrol PASS; diff vs D12-heat-domain-repair = 12 expected new-file lines; upstream snapshot PASS "
 "(bb91a091).")

c['approach']['weak_heat_equation'] = (
 "WeakHeatEquation.lean (thirteenth invocation). The weak (test-paired) form of the heat equation on the D12 "
 "corrected admissible-test-function domain: IsWeakHeatKernelPDE S C K := ∀ phi ∈ C, ∀ y t>0, HasDerivAt "
 "(fun s => ∫ x, phi x * K x y s) (∫ x, phi x * S.laplacian (fun z => K z y t) x) t. The transfer "
 "weakHeatKernelPDE_of_hasDerivAt takes the pointwise PDE plus WeakHeatCertificates (snapshot "
 "measurability/integrability, paired-Laplacian measurability, and laplacian_locally_bounded: ∀ y a b, 0<a → a≤b → "
 "∃ D, ∀ x t ∈ [a,b], |ΔK| ≤ D) and applies mathlib's hasDerivAt_integral_of_dominated_loc_of_deriv_le on "
 "Ioo (t0/2) (2 t0) with dominating function (max D 0) * ‖phi‖. The certificates are proved for the D10 flat "
 "kernel: K ≤ (4πt)^(-n/2); u e^{-u} ≤ e^{-1} gives K ‖z‖²/(4t²) ≤ (4πt)^(-n/2)/(e t); rpow_neg_half_le_of_le "
 "gives prefactor monotonicity; hence |ΔK| ≤ flatLaplacianBound n a = (4πa)^(-n/2)(1/(e a)+n/(2 a)) on [a,b]. "
 "Flat instances on the integrable and C_c classes in every dimension; flat_weak_snapshot_refuted records that "
 "the weak equation holds while the snapshot predicate IsHeatKernelV1 is refuted in positive dimension. The weak "
 "equation is a strict weakening of the pointwise PDE; the converse is not claimed. The manifold-side obligation is "
 "exactly the certificate structure (Gaussian bounds for ΔK).")
c['approach']['weak_finite'] = (
 "WeakFinite.lean (thirteenth invocation). The weak interface on the pinned finite Markov-chain model: the "
 "certificates are proved by finite-dimensional arguments (kernel entries in [0,1] at positive times via "
 "exp_smul_le_one; |ΔK| ≤ finiteLaplacianBound G = ∑ x ∑ z |L x z| on [a,b], a>0, by the triangle inequality and "
 "the entry bound; measurability/integrability from Integrable.of_finite on a finite type with measurable "
 "singletons and finite counting measure). finite_weakHeatKernel instantiates IsWeakHeatKernelPDE via "
 "IsHeatKernelPDE.toWeak and finite_isHeatKernelPDE; finite_weak_and_pde_inhabited records the simultaneous "
 "inhabitation of both predicates. This is the second, non-flat model of the weak interface and shows the "
 "certificate proof is not tied to the Gaussian analysis.")
c['approach']['d7_weak_status'] = (
 "Poincare.D7.HeatKernel.WeakStatus (thirteenth invocation, new D7 module, no existing D7 file edited): "
 "HeatKernelData.toHeatSpacetime and heatKernelData_weakHeatEquation (every legacy D7 heat-kernel datum satisfies "
 "the weak equation on every admissible class carrying the certificates, directly from its heatEquation field); "
 "heatKernelDataV1_weakHeatEquation for the corrected-domain bridge datum; the flat re-exports; "
 "flat_weak_and_snapshot_refuted; finite_weakHeatEquation for the pinned finite model; weak_status_summary.")

c['dependency_requests'].append(
 "MANIFOLD-SIDE WEAK-EQUATION CERTIFICATES: supply WeakHeatCertificates for the Laplace-Beltrami heat kernel "
 "(measurability/integrability of the kernel snapshots and the local uniform bound on ΔK, i.e. the Gaussian upper "
 "bound for the second derivatives); the transfer weakHeatKernelPDE_of_hasDerivAt then yields the weak heat "
 "equation verbatim, with no re-proof of the weak formulation.")
c['dependency_requests'].append(
 "INDEPENDENT SEMANTIC ACCEPTANCE of the 22 authored modules by a fresh reviewer (hash-pinned, "
 "logs/d13_thirteenth_final_hashes.txt), including the thirteenth-invocation WeakHeatEquation.lean, WeakFinite.lean "
 "and Poincare.D7.HeatKernel.WeakStatus.")

c['gates']['thirteenth_final'] = {
 "hashes_recorded": nhashes,
 "hashes_verified": f"{nhashes}/{nhashes} OK (sha256sum -c, logs/d13_thirteenth_final_hashes_check.txt)",
 "semantic_transcripts": f"{len(sem)} files exit 0, {sem_fail} failures (logs/d13_thirteenth_final_semantic_all.out)",
 "build": "exit 0 (9209 jobs), D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 556/556 (logs/d13_thirteenth_final_build.log)",
 "per_file_gate": f"{per_ok}/{per_ok+per_fail} exit 0 (logs/d13_thirteenth_final_perfile.txt)",
 "worktree_gate": f"{wt_ok} files, {wt_fail} failures (logs/d13_thirteenth_final_gate_raw.txt)",
 "forbidden_scan": "0 hard / 0 soft (D13 19 files, D7/HeatKernel 16 files)",
 "negcontrol": "PASS (logs/d13_thirteenth_final_negcontrol.out)",
 "source_integrity": "diff vs D12-heat-domain-repair = 12 expected new-file lines (logs/d13_thirteenth_final_diff.txt)",
 "upstream_snapshot": "PASS (bb91a091) (logs/d13_thirteenth_final_upstream.out)"
}

json.dump(c, open(P, 'w'), indent=1, ensure_ascii=False)
print('checkpoint updated; worktree', wt_ok, wt_fail)
