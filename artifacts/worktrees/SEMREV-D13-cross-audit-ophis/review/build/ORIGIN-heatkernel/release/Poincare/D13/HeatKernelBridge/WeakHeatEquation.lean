/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.PDERepair

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.WeakHeatEquation

**D13 heat-kernel bridge, companion note 3: the weak (test-paired) heat equation on the corrected
admissible-test-function domain.**

`PDERepair.lean` replaced the defective D7 snapshot field by the pointwise PDE
`∂_t K(x,y,t) = Δ_x K(x,y,t)`. The pointwise form is the right *predicate*, but it is not the form
in which the heat equation is consumed by semigroup and parabolic arguments: those pair the
equation against a test function and integrate in space, i.e. they use

`d/dt ∫ x, φ x * K x y t = ∫ x, φ x * Δ_x K(·,y,t) x`   for every admissible `φ`.

This file defines that **weak equation** as a versioned predicate
`IsWeakHeatKernelPDE` (v1) over the D12 corrected domain and proves:

* `weakHeatKernelPDE_of_hasDerivAt`: the pointwise PDE implies the weak equation, provided the
  *analytic certificates* `WeakHeatCertificates` hold. The certificates are exactly the hypotheses
  of mathlib's parametric-integral theorem
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`: measurability and integrability of the
  kernel snapshots, measurability of the paired Laplacian, and a **local uniform bound on the
  paired Laplacian in a compact time interval** `[a,b]` with `a > 0`. The last one is the analytic
  content that, on a Riemannian manifold, is supplied by the Gaussian upper bounds for `∇K`/`ΔK`;
  it is an explicit hypothesis here and is *proved* for the D10 Euclidean kernel below. The
  differentiation under the integral sign is then genuinely mathlib's dominated-convergence
  theorem, not an assumption;
* `IsHeatKernelPDE.toWeak`: every inhabitant of the PDE-repaired D7 predicate satisfies the weak
  equation on its own admissible class, hence on every admissible subclass;
* the flat D10 model: `flatKernel_snapshot_le_prefactor`, `flatKernel_laplacian_bound` and
  `flat_weakHeatCertificates` prove the certificates for the explicit Gaussian kernel (the uniform
  bound `|ΔK(x,y,t)| ≤ (4πa)^(-n/2) (1/(e a) + n/(2a))` on `t ∈ [a,b]`, `a > 0`), so
  `flat_weakHeatKernel_integrable` / `flat_weakHeatKernel_cc` inhabit the weak equation in every
  dimension on both standard admissible classes;
* `flat_weak_snapshot_refuted`: in positive dimension the same kernel satisfies the weak equation
  while the legacy snapshot predicate is refuted — the weak formulation is aligned with the
  repaired PDE predicate, not with the defective field.

**Scope and honesty.** The weak equation is a *weakening* of the pointwise PDE: it is what the
interface can hand to a downstream integration-by-parts argument. The converse (weak ⇒ pointwise)
is not claimed and is false in general without further regularity. This file closes no named
blocker: manifold heat-kernel existence (the Laplace–Beltrami operator, Gaussian bounds,
parabolic regularity) remains open; what is checked is the exact transfer of the D10 Euclidean
kernel to the weak form of the D7 interface on the corrected domain, with the manifold-side
analytic input isolated in one named certificate. All proofs are complete: no `sorry`, `axiom`,
`unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter Real
open scoped Topology Laplacian

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel
open Poincare.D10.HeatKernelEuclidean
open HeatKernelDataV1

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-- The version tag of the weak (test-paired) heat-equation predicate. Bump this only in a *new*
versioned definition; the legacy D7 predicates keep their names and are never edited. -/
def IsWeakHeatKernelPDE.v1 : ℕ := 1

/-- **The weak (test-paired) heat equation on an admissible-test-function class (v1).** For every
admissible test function `φ` and every source point `y`, the spatial pairing
`t ↦ ∫ x, φ x * K x y t` is differentiable at every positive time with derivative the pairing of
`φ` against the Laplacian snapshot `Δ_x K(·,y,t)`. This is the distributional form of the heat
equation: it pairs the pointwise PDE of `IsHeatKernelPDE` against the corrected test-function
domain of `AdmissibleTestClass`. -/
structure IsWeakHeatKernelPDE (S : HeatSpacetime M)
    (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ) : Prop where
  /-- The paired heat equation: `d/dt ∫ φ K(·,y,t) = ∫ φ ΔK(·,y,t)` at every `t > 0`. -/
  weak_solvesPDE : ∀ (φ : M → ℝ), C.cls φ → ∀ y t, 0 < t →
    HasDerivAt (fun s : ℝ => ∫ x, φ x * K x y s ∂S.volume)
      (∫ x, φ x * S.laplacian (fun z => K z y t) x ∂S.volume) t

/-- **The analytic certificates for the weak heat equation.** These are exactly the hypotheses of
mathlib's dominated-differentiation theorem, isolated as a named structure so that the
manifold-side obligation is explicit:

* `snapshot_measurable`, `snapshot_integrable`: the kernel snapshot against an admissible test
  function is measurable and integrable;
* `laplacian_measurable`: the paired Laplacian snapshot is measurable;
* `laplacian_locally_bounded`: on every compact time interval `[a,b]` with `a > 0` the paired
  Laplacian is uniformly bounded in space and time. On a closed Riemannian manifold this is the
  Gaussian upper bound for `ΔK`; for the D10 Euclidean kernel it is proved below. -/
structure WeakHeatCertificates (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume)
    (K : M → M → ℝ → ℝ) : Prop where
  /-- Kernel snapshots against admissible test functions are ae-measurable. -/
  snapshot_measurable : ∀ (φ : M → ℝ), C.cls φ → ∀ y t, 0 < t →
    AEStronglyMeasurable (fun x => φ x * K x y t) S.volume
  /-- Kernel snapshots against admissible test functions are integrable. -/
  snapshot_integrable : ∀ (φ : M → ℝ), C.cls φ → ∀ y t, 0 < t →
    Integrable (fun x => φ x * K x y t) S.volume
  /-- Paired Laplacian snapshots are ae-measurable. -/
  laplacian_measurable : ∀ (φ : M → ℝ), C.cls φ → ∀ y t, 0 < t →
    AEStronglyMeasurable (fun x => φ x * S.laplacian (fun z => K z y t) x) S.volume
  /-- Local uniform bound on the paired Laplacian over a compact time interval `[a,b]`, `a > 0`. -/
  laplacian_locally_bounded : ∀ y a b, 0 < a → a ≤ b → ∃ D, ∀ x t, t ∈ Set.Icc a b →
    |S.laplacian (fun z => K z y t) x| ≤ D

/-- **The pointwise PDE implies the weak equation** on the corrected admissible-test-function
domain, under the analytic certificates. The proof is mathlib's dominated differentiation under
the integral sign: on the time interval `[t₀/2, 2t₀]` the paired Laplacian is uniformly bounded by
`D`, so `D * ‖φ‖` is an integrable dominating function, and the pointwise PDE supplies the
ae-differentiability. No analytic input is assumed beyond the certificates. -/
theorem weakHeatKernelPDE_of_hasDerivAt {S : HeatSpacetime M}
    {C : AdmissibleTestClass M S.volume} {K : M → M → ℝ → ℝ}
    (hpde : ∀ x y t, 0 < t →
      HasDerivAt (fun s : ℝ => K x y s) (S.laplacian (fun z => K z y t) x) t)
    (hc : WeakHeatCertificates S C K) :
    IsWeakHeatKernelPDE S C K := by
  refine ⟨fun φ hφ y t₀ ht₀ => ?_⟩
  obtain ⟨D, hD⟩ := hc.laplacian_locally_bounded y (t₀ / 2) (2 * t₀) (by linarith) (by linarith)
  have hDle : ∀ x t, t ∈ Set.Icc (t₀ / 2) (2 * t₀) →
      |S.laplacian (fun z => K z y t) x| ≤ max D 0 :=
    fun x t ht => le_trans (hD x t ht) (le_max_left _ _)
  have hs : Set.Ioo (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
  have hbound_int : Integrable (fun x => max D 0 * ‖φ x‖) S.volume :=
    (C.cls_integrable hφ).norm.const_mul (max D 0)
  have hF_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun x => φ x * K x y t) S.volume := by
    filter_upwards [isOpen_Ioi.mem_nhds ht₀] with t ht
    exact hc.snapshot_measurable φ hφ y t ht
  have hF_int : Integrable (fun x => φ x * K x y t₀) S.volume :=
    hc.snapshot_integrable φ hφ y t₀ ht₀
  have hF'_meas :
      AEStronglyMeasurable (fun x => φ x * S.laplacian (fun z => K z y t₀) x) S.volume :=
    hc.laplacian_measurable φ hφ y t₀ ht₀
  have h_bound : ∀ᵐ x ∂S.volume, ∀ t ∈ Set.Ioo (t₀ / 2) (2 * t₀),
      ‖φ x * S.laplacian (fun z => K z y t) x‖ ≤ max D 0 * ‖φ x‖ := by
    filter_upwards with x
    intro t ht
    have hb : |S.laplacian (fun z => K z y t) x| ≤ max D 0 :=
      hDle x t (Set.Ioo_subset_Icc_self ht)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |φ x| * |S.laplacian (fun z => K z y t) x| ≤ |φ x| * max D 0 := by gcongr
      _ = max D 0 * |φ x| := by ring
  have h_diff : ∀ᵐ x ∂S.volume, ∀ t ∈ Set.Ioo (t₀ / 2) (2 * t₀),
      HasDerivAt (fun s : ℝ => φ x * K x y s)
        (φ x * S.laplacian (fun z => K z y t) x) t := by
    filter_upwards with x
    intro t ht
    have htpos : 0 < t := lt_trans (by linarith) ht.1
    exact (hpde x y t htpos).const_mul (φ x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ) (α := M) (F := fun t x => φ x * K x y t)
    (F' := fun t x => φ x * S.laplacian (fun z => K z y t) x)
    (bound := fun x => max D 0 * ‖φ x‖) (s := Set.Ioo (t₀ / 2) (2 * t₀)) (x₀ := t₀)
    (μ := S.volume) hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

namespace IsHeatKernelPDE

/-- **The PDE-repaired predicate implies the weak equation.** Every inhabitant of
`IsHeatKernelPDE` satisfies the weak (test-paired) heat equation on its own admissible class, once
the analytic certificates hold for that class. -/
theorem toWeak {S : HeatSpacetime M} {C : AdmissibleTestClass M S.volume} {K : M → M → ℝ → ℝ}
    (h : IsHeatKernelPDE S C K) (hc : WeakHeatCertificates S C K) :
    IsWeakHeatKernelPDE S C K :=
  weakHeatKernelPDE_of_hasDerivAt (fun x y t ht => h.solvesPDE x y t ht) hc

end IsHeatKernelPDE

namespace IsWeakHeatKernelPDE

/-- Restatement of the weak equation field as a named `HasDerivAt` lemma (used by consumers). -/
theorem hasDerivAt {S : HeatSpacetime M} {C : AdmissibleTestClass M S.volume}
    {K : M → M → ℝ → ℝ} (h : IsWeakHeatKernelPDE S C K) (φ : M → ℝ) (hφ : C.cls φ) (y : M)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ x, φ x * K x y s ∂S.volume)
      (∫ x, φ x * S.laplacian (fun z => K z y t) x ∂S.volume) t :=
  h.weak_solvesPDE φ hφ y t ht

/-- The weak equation is inherited by every admissible subclass: if `C' ⊆ C` then a weak solution
on `C` is a weak solution on `C'`. In particular the integrable-class weak equation implies the
`C_c` one. -/
theorem mono_class {S : HeatSpacetime M} {C C' : AdmissibleTestClass M S.volume}
    {K : M → M → ℝ → ℝ} (h : IsWeakHeatKernelPDE S C K)
    (hsub : ∀ f : M → ℝ, C'.cls f → C.cls f) : IsWeakHeatKernelPDE S C' K :=
  ⟨fun φ hφ => h.weak_solvesPDE φ (hsub φ hφ)⟩

end IsWeakHeatKernelPDE

/-! ## The explicit D10 Euclidean kernel satisfies the weak equation

The analytic certificates are proved for the Gaussian in this section. The only genuinely
analytic input is the local uniform bound on `ΔK` on a compact time interval, which is the
one-dimensional inequality `u e^{-u} ≤ e^{-1}` together with the prefactor monotonicity of the
Gaussian. -/

/-- The Gaussian prefactor is bounded by its value at the left endpoint of a positive time
interval: for `0 < a ≤ t`, `(4πt)^{-n/2} ≤ (4πa)^{-n/2}`. -/
theorem rpow_neg_half_le_of_le (n : ℕ) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    (4 * π * t) ^ (-(n : ℝ) / 2) ≤ (4 * π * a) ^ (-(n : ℝ) / 2) := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hbase : (4 * π * a) ^ ((n : ℝ) / 2) ≤ (4 * π * t) ^ ((n : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) (by positivity)
  have hposa : 0 < (4 * π * a) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hpost : 0 < (4 * π * t) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * π * t) ((n : ℝ) / 2),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * π * a) ((n : ℝ) / 2)]
  exact (inv_le_inv₀ hpost hposa).mpr hbase

/-- The elementary maximum `u e^{-u} ≤ e^{-1}` on `u ≥ 0`. -/
theorem mul_exp_neg_le_inv_e (u : ℝ) (hu : 0 ≤ u) : u * Real.exp (-u) ≤ Real.exp (-1) := by
  have h : u ≤ Real.exp (u - 1) := by
    have h1 := Real.add_one_le_exp (u - 1)
    linarith
  calc u * Real.exp (-u) ≤ Real.exp (u - 1) * Real.exp (-u) := by gcongr
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- **Gaussian upper bound for the explicit D10 kernel**: `K ≤ (4πt)^{-n/2}` at positive times,
by the exponential factor being at most one. -/
theorem gaussianKernel_le_prefactor (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    gaussianKernel n t z ≤ (4 * π * t) ^ (-(n : ℝ) / 2) := by
  rw [gaussianKernel_apply]
  have hexp : Real.exp (-‖z‖ ^ 2 / (4 * t)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hz : 0 ≤ ‖z‖ ^ 2 / (4 * t) := by positivity
    rw [neg_div]
    exact neg_nonpos.mpr hz
  have hpre : 0 ≤ (4 * π * t) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  calc (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
      ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * 1 := by gcongr
    _ = (4 * π * t) ^ (-(n : ℝ) / 2) := mul_one _

/-- The absolute value form of the Gaussian upper bound. -/
theorem gaussianKernel_abs_le_prefactor (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) : |gaussianKernel n t z| ≤ (4 * π * t) ^ (-(n : ℝ) / 2) := by
  rw [abs_of_nonneg (gaussianKernel_nonneg n ht.le z)]
  exact gaussianKernel_le_prefactor n z ht

/-- The bridge kernel obeys the same upper bound at positive times. -/
theorem flatKernel_abs_le_prefactor (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) : |flatKernel n x y t| ≤ (4 * π * t) ^ (-(n : ℝ) / 2) := by
  rw [flatKernel_of_pos n x y ht]
  exact gaussianKernel_abs_le_prefactor n (x - y) ht

/-- The uniform bound on the Laplacian of the D10 kernel over the time interval `[a,b]`,
`a > 0`: `(4πa)^{-n/2} (1/(e a) + n/(2a))`. -/
noncomputable def flatLaplacianBound (n : ℕ) (a : ℝ) : ℝ :=
  (4 * π * a) ^ (-(n : ℝ) / 2) * (1 / (Real.exp 1 * a) + (n : ℝ) / (2 * a))

/-- **The explicit Laplacian of the bridge kernel**, in the form used for the bound. -/
theorem flatHeatSpacetime_laplacian_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    (flatHeatSpacetime n).laplacian (fun z => flatKernel n z y t) x =
      gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
  rw [flatHeatSpacetime_laplacian, flatHeatKernelCore_laplacian,
    laplacianLinearMap_flatKernel n ht y]
  change Δ (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (z - y)) x =
    gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))
  rw [laplacian_comp_sub (gaussianKernel n t) y x, laplacian_gaussianKernel n ht (x - y)]

/-- Continuity in the space variable of the bridge-kernel snapshot. -/
theorem flatKernel_continuous_snapshot (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) : Continuous (fun x : EuclideanSpace ℝ (Fin n) => flatKernel n x y t) := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) => flatKernel n x y t)
      = fun x => gaussianKernel n t (x - y) := by
    funext x
    exact flatKernel_of_pos n x y ht
  rw [hfun]
  exact (continuous_gaussianKernel n).comp (continuous_id.sub continuous_const)

/-- Continuity in the space variable of the Laplacian snapshot of the bridge kernel. -/
theorem flatKernel_laplacian_continuous_snapshot (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (flatHeatSpacetime n).laplacian (fun z => flatKernel n z y t) x) := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) =>
        (flatHeatSpacetime n).laplacian (fun z => flatKernel n z y t) x)
      = fun x => gaussianKernel n t (x - y) *
          (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
    funext x
    exact flatHeatSpacetime_laplacian_apply n y ht x
  rw [hfun]
  have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ‖x - y‖ ^ 2) :=
    ((continuous_id.sub continuous_const).norm).pow 2
  exact ((continuous_gaussianKernel n).comp (continuous_id.sub continuous_const)).mul
    ((h1.div_const (4 * t ^ 2)).sub continuous_const)

/-- The first term of the Laplacian bound: `K(z) ‖z‖²/(4t²) ≤ (4πt)^{-n/2} / (e t)`, from
`u e^{-u} ≤ e^{-1}` with `u = ‖z‖²/(4t)`. -/
theorem gaussianKernel_mul_sq_div_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) :
    gaussianKernel n t z * (‖z‖ ^ 2 / (4 * t ^ 2)) ≤
      (4 * π * t) ^ (-(n : ℝ) / 2) * (1 / (Real.exp 1 * t)) := by
  have hz : 0 ≤ ‖z‖ ^ 2 / (4 * t) := by positivity
  have hK : gaussianKernel n t z
      = (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) := by
    rw [gaussianKernel_apply]
    congr 1
    rw [neg_div]
  have hfac : ‖z‖ ^ 2 / (4 * t ^ 2) = (‖z‖ ^ 2 / (4 * t)) / t := by
    field_simp
  rw [hK, hfac]
  have hsplit : (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) *
      ((‖z‖ ^ 2 / (4 * t)) / t)
      = (4 * π * t) ^ (-(n : ℝ) / 2) * (1 / t) *
        ((‖z‖ ^ 2 / (4 * t)) * Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by ring
  rw [hsplit]
  have hexp : (‖z‖ ^ 2 / (4 * t)) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) ≤ Real.exp (-1) :=
    mul_exp_neg_le_inv_e _ hz
  calc (4 * π * t) ^ (-(n : ℝ) / 2) * (1 / t) *
        ((‖z‖ ^ 2 / (4 * t)) * Real.exp (-(‖z‖ ^ 2 / (4 * t))))
      ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * (1 / t) * Real.exp (-1) := by gcongr
    _ = (4 * π * t) ^ (-(n : ℝ) / 2) * (1 / (Real.exp 1 * t)) := by
        rw [Real.exp_neg]; ring

/-- **Local uniform bound on the Laplacian of the D10 kernel.** For `0 < a ≤ t` and every space
point, `|Δ_x K(x,y,t)| ≤ flatLaplacianBound n a`. -/
theorem flatKernel_laplacian_abs_le (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) {a b t : ℝ}
    (ha : 0 < a) (ht : t ∈ Set.Icc a b) (x : EuclideanSpace ℝ (Fin n)) :
    |(flatHeatSpacetime n).laplacian (fun z => flatKernel n z y t) x| ≤ flatLaplacianBound n a := by
  have htpos : 0 < t := lt_of_lt_of_le ha ht.1
  have hpre : (4 * π * t) ^ (-(n : ℝ) / 2) ≤ (4 * π * a) ^ (-(n : ℝ) / 2) :=
    rpow_neg_half_le_of_le n ha ht.1
  have hprepos : 0 ≤ (4 * π * t) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have hpreapos : 0 ≤ (4 * π * a) ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  -- the two terms
  set u : ℝ := ‖x - y‖ ^ 2 / (4 * t) with hu
  have hu_nonneg : 0 ≤ u := by positivity
  have hK : gaussianKernel n t (x - y) = (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-u) := by
    rw [gaussianKernel_apply]
    congr 1
    rw [hu, neg_div]
  have hs : ‖x - y‖ ^ 2 / (4 * t ^ 2) = u / t := by
    rw [hu]; field_simp
  have hfirst : |gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2))|
      ≤ (4 * π * a) ^ (-(n : ℝ) / 2) * (1 / (Real.exp 1 * a)) := by
    have harg : 0 ≤ ‖x - y‖ ^ 2 / (4 * t ^ 2) := by positivity
    rw [abs_of_nonneg (mul_nonneg (gaussianKernel_nonneg n htpos.le _) harg)]
    calc gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2))
        ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * (1 / (Real.exp 1 * t)) :=
          gaussianKernel_mul_sq_div_le n htpos (x - y)
      _ ≤ (4 * π * a) ^ (-(n : ℝ) / 2) * (1 / (Real.exp 1 * a)) := by
          have hinv : 1 / (Real.exp 1 * t) ≤ 1 / (Real.exp 1 * a) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left ht.1 (Real.exp_pos 1).le)
          exact mul_le_mul hpre hinv (by positivity) hpreapos
  have hsecond : |gaussianKernel n t (x - y) * ((n : ℝ) / (2 * t))|
      ≤ (4 * π * a) ^ (-(n : ℝ) / 2) * ((n : ℝ) / (2 * a)) := by
    have harg : 0 ≤ (n : ℝ) / (2 * t) := by positivity
    rw [abs_of_nonneg (mul_nonneg (gaussianKernel_nonneg n htpos.le _) harg)]
    have hKle : gaussianKernel n t (x - y) ≤ (4 * π * t) ^ (-(n : ℝ) / 2) :=
      gaussianKernel_le_prefactor n (x - y) htpos
    calc gaussianKernel n t (x - y) * ((n : ℝ) / (2 * t))
        ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * ((n : ℝ) / (2 * t)) := by gcongr
      _ ≤ (4 * π * a) ^ (-(n : ℝ) / 2) * ((n : ℝ) / (2 * a)) := by
          have hdiv : (n : ℝ) / (2 * t) ≤ (n : ℝ) / (2 * a) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [ht.1])
          exact mul_le_mul hpre hdiv (by positivity) hpreapos
  have htri : |gaussianKernel n t (x - y) *
        (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))|
      ≤ |gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2))|
        + |gaussianKernel n t (x - y) * ((n : ℝ) / (2 * t))| := by
    have h := abs_add_le (gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2)))
      (-(gaussianKernel n t (x - y) * ((n : ℝ) / (2 * t))))
    have h1 : gaussianKernel n t (x - y) *
          (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))
        = gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2))
          + -(gaussianKernel n t (x - y) * ((n : ℝ) / (2 * t))) := by ring
    rw [h1]
    simpa only [abs_neg] using h
  rw [flatHeatSpacetime_laplacian_apply n y htpos x]
  calc |gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))|
      ≤ |gaussianKernel n t (x - y) * (‖x - y‖ ^ 2 / (4 * t ^ 2))|
        + |gaussianKernel n t (x - y) * ((n : ℝ) / (2 * t))| := htri
    _ ≤ (4 * π * a) ^ (-(n : ℝ) / 2) * (1 / (Real.exp 1 * a))
        + (4 * π * a) ^ (-(n : ℝ) / 2) * ((n : ℝ) / (2 * a)) := add_le_add hfirst hsecond
    _ = flatLaplacianBound n a := by
        rw [flatLaplacianBound]; ring

/-- **The analytic certificates for the flat D10 kernel**, for any admissible class whose members
are continuous and integrable (in particular the integrable class itself and the `C_c` class). -/
theorem flatWeakHeatCertificates_of_subclass (n : ℕ)
    (C : AdmissibleTestClass (EuclideanSpace ℝ (Fin n)) (flatHeatSpacetime n).volume)
    (hsub : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, C.cls f →
      (AdmissibleTestClass.continuousIntegrableClass
        (flatHeatSpacetime n).volume).cls f) :
    WeakHeatCertificates (flatHeatSpacetime n) C (flatKernel n) where
  snapshot_measurable := by
    intro φ hφ y t ht
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => φ x * flatKernel n x y t) :=
      (hsub φ hφ).1.mul (flatKernel_continuous_snapshot n y ht)
    exact hcont.aemeasurable.aestronglyMeasurable
  snapshot_integrable := by
    intro φ hφ y t ht
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => φ x * flatKernel n x y t) :=
      (hsub φ hφ).1.mul (flatKernel_continuous_snapshot n y ht)
    have hφint : Integrable φ (flatHeatSpacetime n).volume := (hsub φ hφ).2
    refine Integrable.mono'
      (g := fun x => (4 * π * t) ^ (-(n : ℝ) / 2) * ‖φ x‖) ?_
      hcont.aemeasurable.aestronglyMeasurable ?_
    · exact hφint.norm.const_mul _
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      have hKle := flatKernel_abs_le_prefactor n x y ht
      calc |φ x| * |flatKernel n x y t| ≤ |φ x| * (4 * π * t) ^ (-(n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hKle (abs_nonneg _)
        _ = (4 * π * t) ^ (-(n : ℝ) / 2) * ‖φ x‖ := by rw [Real.norm_eq_abs]; ring
  laplacian_measurable := by
    intro φ hφ y t ht
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        φ x * (flatHeatSpacetime n).laplacian (fun z => flatKernel n z y t) x) :=
      (hsub φ hφ).1.mul (flatKernel_laplacian_continuous_snapshot n y ht)
    exact hcont.aemeasurable.aestronglyMeasurable
  laplacian_locally_bounded := by
    intro y a b ha hab
    refine ⟨flatLaplacianBound n a, fun x t ht =>
      flatKernel_laplacian_abs_le n y ha ht x⟩

/-- The flat certificates on the continuous-integrable class. -/
theorem flatWeakHeatCertificates_integrable (n : ℕ) :
    WeakHeatCertificates (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
      (flatKernel n) :=
  flatWeakHeatCertificates_of_subclass n _ (fun _ hf => hf)

/-- The flat certificates on the continuous-compact-support class. -/
theorem flatWeakHeatCertificates_cc (n : ℕ) :
    WeakHeatCertificates (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousCompactSupportClass
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (flatKernel n) := by
  haveI : IsFiniteMeasureOnCompacts (flatHeatSpacetime n).volume :=
    (inferInstance : IsFiniteMeasureOnCompacts (volume : Measure (EuclideanSpace ℝ (Fin n))))
  exact flatWeakHeatCertificates_of_subclass n _ (fun f hf =>
    AdmissibleTestClass.continuousCompactSupportClass_subset_continuousIntegrableClass f hf)

/-- **The D10 Euclidean heat kernel satisfies the weak heat equation in every dimension**
(continuous-integrable class): the transfer `IsHeatKernelPDE.toWeak` applied to the repaired flat
predicate `flat_isHeatKernelPDE_integrable` and the proved flat certificates. -/
theorem flat_weakHeatKernel_integrable (n : ℕ) :
    IsWeakHeatKernelPDE (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
      (flatKernel n) :=
  (flat_isHeatKernelPDE_integrable n).toWeak (flatWeakHeatCertificates_integrable n)

/-- **The D10 Euclidean heat kernel satisfies the weak heat equation on the `C_c` class in every
dimension.** -/
theorem flat_weakHeatKernel_cc (n : ℕ) :
    IsWeakHeatKernelPDE (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousCompactSupportClass
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (flatKernel n) :=
  (flat_isHeatKernelPDE_cc n).toWeak (flatWeakHeatCertificates_cc n)

/-- **The weak equation on every admissible subclass of the integrable class**, for the flat D10
kernel (in particular on the `C_c` class after rewriting the volume). -/
theorem flat_weakHeatKernel_of_subclass (n : ℕ)
    (C : AdmissibleTestClass (EuclideanSpace ℝ (Fin n)) (flatHeatSpacetime n).volume)
    (hsub : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, C.cls f →
      (AdmissibleTestClass.continuousIntegrableClass
        (flatHeatSpacetime n).volume).cls f) :
    IsWeakHeatKernelPDE (flatHeatSpacetime n) C (flatKernel n) :=
  (flat_weakHeatKernel_integrable n).mono_class hsub

/-- **The weak formulation is aligned with the repaired predicate, not with the defective
snapshot field.** In every positive dimension the D10 kernel satisfies the weak heat equation on
the corrected admissible domain while the legacy snapshot predicate is refuted by the same kernel
on the same flat spacetime. -/
theorem flat_weak_snapshot_refuted (n : ℕ) (hn : 0 < n) :
    IsWeakHeatKernelPDE (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) ∧
      ¬ IsHeatKernelV1 (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) :=
  ⟨flat_weakHeatKernel_integrable n, flatHeatSpacetime_not_isHeatKernelV1_integrableClass n hn⟩

end Poincare.D13.HeatKernelBridge
