
## 25. Thirteenth invocation (2026-09-12T00:10+08:00, elapsed ≈ 1.4 h): the weak (test-paired) heat equation on the corrected admissible-test-function domain

### 25.1 Baseline re-verification before any change

The frozen twelfth-invocation artifact was re-verified before any edit. All **30/30** hashes of
`logs/d13_twelfth_final_hashes.txt` were re-computed byte-identical (`sha256sum -c` from the
worktree root: `logs/d13_thirteenth_baseline_hashes_check.txt`, all `OK`), and the full release
build was re-run: exit 0, `Build completed successfully (9206 jobs)`, `D6AUDIT VERDICT PASS`
(`logs/d13_thirteenth_baseline_build.log`). No baseline file was modified.

### 25.2 The gap: the pointwise PDE is not the form the equation is consumed in

`PDERepair.lean` (fourth invocation) repaired the defective D7 snapshot field by the genuine
pointwise PDE

`∂_t K(x,y,t) = Δ_x K(x,y,t)`   (`t > 0`),

and `IsHeatKernelPDE` records it as `HasDerivAt (fun s => K x y s) (Δ_x K(·,y,t) x) t` **at each
space point `x`**. That is the right *predicate*, but it is not the form in which the heat equation
is consumed downstream: semigroup, Duhamel and parabolic-regularity arguments pair the equation
against a test function and differentiate the *spatial pairing* under the integral sign, i.e. they
use

`d/dt ∫ x, φ x * K x y t = ∫ x, φ x * Δ_x K(·,y,t) x`   for every admissible `φ`.

The passage from the pointwise identity to this weak identity is **not** formal: it needs
measurability and integrability of the kernel snapshots, measurability of the paired Laplacian, and
a **local uniform bound on `Δ_x K` on a compact time interval `[a,b]`, `a > 0`**. On a Riemannian
manifold the last item is precisely a Gaussian upper bound for `ΔK` — one of the named missing
inputs of `D7-HEAT-KERNEL-EXISTENCE`. The thirteenth invocation isolates that input as an explicit
certificate, proves the transfer with mathlib's dominated differentiation theorem, and proves the
certificates for the explicit D10 Euclidean kernel in every dimension **and** for the pinned finite
model.

### 25.3 The weak predicate and the transfer (proved)

`release/Poincare/D13/HeatKernelBridge/WeakHeatEquation.lean`:

* **`IsWeakHeatKernelPDE` (v1)** — the weak equation as a versioned predicate over the D12
  corrected domain: for every admissible test function `φ` (an `AdmissibleTestClass` member, hence
  continuous and integrable) and every source point `y`, the pairing `t ↦ ∫ x, φ x * K x y t` is
  differentiable at every `t > 0` with derivative `∫ x, φ x * Δ_x K(·,y,t) x`;
* **`WeakHeatCertificates`** — the four analytic certificates, exactly the hypotheses of mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`: snapshot measurability, snapshot
  integrability, paired-Laplacian measurability, and the local uniform bound
  `∀ y a b, 0 < a → a ≤ b → ∃ D, ∀ x t ∈ [a,b], |Δ_x K(·,y,t) x| ≤ D`. This is the *only*
  analytic input; nothing equivalent to the conclusion is assumed;
* **`weakHeatKernelPDE_of_hasDerivAt`** — the transfer: a pointwise PDE plus the certificates imply
  the weak equation. The proof applies the parametric-integral theorem on the neighbourhood
  `Ioo (t₀/2) (2t₀) ∋ t₀`; the dominating function is `max D 0 * ‖φ x‖`, integrable because `φ` is
  admissible, and the ae-differentiability is the pointwise PDE multiplied by the constant `φ x`.
  Nothing is postulated: the differentiation under the integral is mathlib's theorem;
* **`IsHeatKernelPDE.toWeak`** — every inhabitant of the repaired D7 predicate satisfies the weak
  equation on its own class; **`IsWeakHeatKernelPDE.hasDerivAt`** restates the field;
  **`IsWeakHeatKernelPDE.mono_class`** transfers the weak equation to every admissible subclass
  (in particular from the integrable class to `C_c`).

### 25.4 The flat D10 instance (certificates proved, all dimensions)

The certificates are *proved* for the explicit Gaussian, so the D10 kernel inhabits the weak
equation unconditionally in every dimension:

* `gaussianKernel_le_prefactor` / `gaussianKernel_abs_le_prefactor` / `flatKernel_abs_le_prefactor`:
  `K(x,y,t) ≤ (4πt)^{-n/2}` at positive times (the exponential factor is at most one);
* `mul_exp_neg_le_inv_e`: the elementary maximum `u e^{-u} ≤ e^{-1}` on `u ≥ 0` (from
  `u ≤ e^{u-1}`), and `gaussianKernel_mul_sq_div_le`:
  `K(z) ‖z‖²/(4t²) ≤ (4πt)^{-n/2} / (e t)` — the first term of `ΔK`;
* `flatLaplacianBound n a = (4πa)^{-n/2} (1/(e a) + n/(2a))` and
  **`flatKernel_laplacian_abs_le`**: for `0 < a ≤ t`,
  `|Δ_x K(x,y,t)| ≤ flatLaplacianBound n a` uniformly in space and time. The proof splits
  `ΔK = K·‖x-y‖²/(4t²) − K·n/(2t)`, bounds the first term by `u e^{-u} ≤ e^{-1}` and the second by
  the Gaussian sup bound, and uses the prefactor monotonicity
  `rpow_neg_half_le_of_le : (4πt)^{-n/2} ≤ (4πa)^{-n/2}` for `0 < a ≤ t`;
* `flatHeatSpacetime_laplacian_apply` (the explicit `ΔK` formula through
  `laplacianLinearMap_flatKernel` and `laplacian_gaussianKernel`),
  `flatKernel_continuous_snapshot`, `flatKernel_laplacian_continuous_snapshot` (continuity in the
  space variable used for the measurability certificates);
* `flatWeakHeatCertificates_of_subclass` (the four certificates for every class contained in the
  continuous-integrable class), its two instances `..._integrable` and `..._cc`, and the instances
  of the weak equation **`flat_weakHeatKernel_integrable`** and **`flat_weakHeatKernel_cc`** in
  every dimension, together with `flat_weakHeatKernel_of_subclass`;
* **`flat_weak_snapshot_refuted`**: in every positive dimension the D10 kernel satisfies the weak
  equation on the corrected domain while the legacy snapshot predicate `IsHeatKernelV1` is refuted
  by the same kernel on the same flat spacetime — the weak formulation is aligned with the repaired
  PDE predicate, not with the defective field.

### 25.5 The pinned finite model: a second, non-flat model of the weak interface

`release/Poincare/D13/HeatKernelBridge/WeakFinite.lean` instantiates the same weak interface on the
pinned finite Markov-chain model of `FiniteSpaceHeat.lean`, with a **structurally different**
certificate proof:

* `finiteHeatKernel_abs_le_one`: every entry of the pinned kernel is in `[0,1]` at positive times
  (nonnegativity plus the Gaussian upper bound `exp_smul_le_one`);
* `finiteLaplacianBound G = ∑ x, ∑ z, |G.L x z|` (finite, nonnegative:
  `finiteLaplacianBound_nonneg`) and **`finiteHeatKernel_laplacian_abs_le`**:
  `|Δ_x K(x,y,t)| ≤ finiteLaplacianBound G` for every `t ∈ [a,b]`, `a > 0`, by the finite triangle
  inequality and the entry bound — no Gaussian analysis;
* `finiteWeakHeatCertificates`: the four certificates, with measurability and integrability from
  `Integrable.of_finite` (finite type, measurable singletons, finite counting measure);
* **`finite_weakHeatKernel`**: the matrix-exponential kernel inhabits `IsWeakHeatKernelPDE` over the
  counting measure, via `IsHeatKernelPDE.toWeak` applied to `finite_isHeatKernelPDE`;
* `finite_weak_and_pde_inhabited`: the weak and the pointwise predicates are inhabited
  simultaneously by the same explicit kernel.

This shows the weak interface is not tied to the Gaussian certificate proof: it is inhabited by a
flat Euclidean family (every dimension) and by a finite reversible Markov chain.

### 25.6 D7-level consumption

New D7-namespaced consumer `release/Poincare/D7/HeatKernel/WeakStatus.lean` (no existing D7 file is
edited):

* `HeatKernelData.toHeatSpacetime` (+ the five `@[simp]` field lemmas): the schematic spacetime
  attached to a legacy D7 datum (`timeDerivative := 0`, unused by the weak equation);
* **`heatKernelData_weakHeatEquation`**: *every* legacy D7 `HeatKernelData` satisfies the weak heat
  equation on every admissible test class carrying the certificates — directly from its
  `heatEquation` field. This is a new D7-level theorem, not a restatement;
* `heatKernelDataV1_weakHeatEquation`: the same for the corrected-domain bridge datum
  `HeatKernelDataV1`, from its D11 core `heatEquation`;
* `flat_weakHeatEquation_integrable` / `flat_weakHeatEquation_cc` and
  `flat_weak_and_snapshot_refuted`: the flat instances re-exported at the D7 level;
* `finite_weakHeatEquation`: the pinned finite model satisfies the weak equation at the D7 level;
* `weak_status_summary`: the D7-level conjunction of the transfer, the two flat class instances and
  the snapshot refutation.

### 25.7 Declaration inventory (45 new declarations, all audited)

`WeakHeatEquation.lean` (25): `IsWeakHeatKernelPDE.v1`, `IsWeakHeatKernelPDE`,
`WeakHeatCertificates`, `weakHeatKernelPDE_of_hasDerivAt`, `IsHeatKernelPDE.toWeak`,
`IsWeakHeatKernelPDE.hasDerivAt`, `IsWeakHeatKernelPDE.mono_class`, `rpow_neg_half_le_of_le`,
`mul_exp_neg_le_inv_e`, `gaussianKernel_le_prefactor`, `gaussianKernel_abs_le_prefactor`,
`flatKernel_abs_le_prefactor`, `flatLaplacianBound`, `flatHeatSpacetime_laplacian_apply`,
`flatKernel_continuous_snapshot`, `flatKernel_laplacian_continuous_snapshot`,
`gaussianKernel_mul_sq_div_le`, `flatKernel_laplacian_abs_le`,
`flatWeakHeatCertificates_of_subclass`, `flatWeakHeatCertificates_integrable`,
`flatWeakHeatCertificates_cc`, `flat_weakHeatKernel_integrable`, `flat_weakHeatKernel_cc`,
`flat_weakHeatKernel_of_subclass`, `flat_weak_snapshot_refuted`.

`WeakFinite.lean` (7): `finiteLaplacianBound`, `finiteLaplacianBound_nonneg`,
`finiteHeatKernel_abs_le_one`, `finiteHeatKernel_laplacian_abs_le`, `finiteWeakHeatCertificates`,
`finite_weakHeatKernel`, `finite_weak_and_pde_inhabited`.

`Poincare.D7.HeatKernel.WeakStatus` (13): `HeatKernelData.toHeatSpacetime` and the five field
lemmas, `heatKernelData_weakHeatEquation`, `heatKernelDataV1_weakHeatEquation`,
`flat_weakHeatEquation_integrable`, `flat_weakHeatEquation_cc`,
`flat_weak_and_snapshot_refuted`, `finite_weakHeatEquation`, `weak_status_summary`.

`AxiomAudit.lean` was extended from 511 to **556** audited declarations (382 → 427 `#print axioms`
lines); `tmp/d13_semantic_checks_n_weak.lean` is the extended semantic transcript.

### 25.8 Honest scope

This is a **proved transfer theorem plus two proved model instances** (flat Euclidean and pinned
finite). It closes no named blocker (`exact_blockers_closed = []`) and does not claim
`D7-HEAT-KERNEL-EXISTENCE`: the certificates are explicit hypotheses for a general datum, and for
the manifold case they are exactly the missing analytic input (measurability/integrability of the
kernel and Gaussian bounds for `ΔK`). It is also honest about the logical strength: the weak
equation is a *weakening* of the pointwise PDE; the converse (weak ⇒ pointwise) is neither proved
nor claimed, and is false without further regularity. What is new and checked is (i) the exact
transfer with mathlib's dominated differentiation, (ii) the four certificates *proved* for the D10
Euclidean kernel with the explicit uniform bound `(4πa)^{-n/2}(1/(e a) + n/(2a))` on `[a,b]`,
`a > 0`, (iii) the flat weak instances on both standard admissible classes in every dimension,
(iv) the certificates and weak instance for the pinned finite model with a different
finite-dimensional proof, and (v) the D7-level legacy and finite transports. All proofs are
complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`; every new declaration
is re-checked by the fail-closed `Lean.collectAxioms` gate inside the standard cone
`[propext, Classical.choice, Quot.sound]`.

### 25.9 Thirteenth-invocation final gates

**All gates green on the frozen thirteenth-invocation artifact** (`logs/d13_thirteenth_final_*`):

- **Source hashes**: __HASHCOUNT__ recorded and re-verified with `sha256sum -c`
  (`logs/d13_thirteenth_final_hashes_check.txt`, all OK);
- **Semantic transcripts**: __SEMCOUNT__ files exit 0, 0 failures
  (`logs/d13_thirteenth_final_semantic_all.out`), including the extended
  `tmp/d13_semantic_checks_n_weak.lean`;
- **Full build**: exit 0, `Build completed successfully (__BUILDJOBS__ jobs)`, D6AUDIT PASS,
  `D13HeatKernelBridgeAxiomCheck PASS 556/556` (`logs/d13_thirteenth_final_build.log`);
- **Per-file gate**: __PERFILE__ (`logs/d13_thirteenth_final_perfile.txt`);
- **Worktree gate**: __WORKTREE__ (`logs/d13_thirteenth_final_gate_raw.txt`);
- **Forbidden scan**: 0 hard / 0 soft for `D13/HeatKernelBridge` and `D7/HeatKernel`
  (`logs/d13_thirteenth_final_forbidden_{d13,d7}.json`);
- **Negative control**: PASS (`logs/d13_thirteenth_final_negcontrol.out`);
- **Source integrity**: `diff -rq release/Poincare` vs `D12-heat-domain-repair` = 12 lines, all
  `Only in` entries — the `D13` tree plus the 11 authored D7 consumer files (including the new
  `WeakStatus.lean`); no file present in the D12 tree was modified
  (`logs/d13_thirteenth_final_diff.txt`);
- **Upstream snapshot**: PASS, commit `bb91a091` (`logs/d13_thirteenth_final_upstream.out`).

### 25.10 Thirteenth-invocation verdict

**Progress on the interface, not closure.** The thirteenth invocation adds the weak
(test-paired) form of the heat equation on the D12 corrected admissible-test-function domain: the
versioned predicate `IsWeakHeatKernelPDE`, the explicit analytic certificates, the proved transfer
from the pointwise PDE by mathlib's dominated differentiation, the proved Gaussian bounds and the
resulting flat D10 instances in every dimension on both standard classes, the same weak equation
for the pinned finite model with a finite-dimensional certificate proof, and the D7-level legacy
and finite transports. 45 new audited declarations (511 → 556), three new files
(`WeakHeatEquation.lean`, `WeakFinite.lean`, `Poincare.D7.HeatKernel.WeakStatus`). It closes no
named blocker and does not claim `D7-HEAT-KERNEL-EXISTENCE`. `exact_blockers_closed = []`.
TASK_DONE is requested only as an independent-acceptance request for this checked increment.
