/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Poincare.D12.HeatSemigroup.L1Contraction

**D12 heat-semigroup analysis, part 2: L¹ contraction and integrability of the heat operator.**

For `t > 0` and an a.e.-strongly-measurable `f : EuclideanSpace ℝ (Fin n) → ℝ` we prove, against
Lebesgue measure `volume`:

* the pointwise bound `‖P_t f x‖ₑ ≤ ∫⁻ y, ‖gaussianKernel n t (x - y) * f y‖ₑ`
  (mathlib's `enorm_integral_le_lintegral_enorm`);
* the **L¹ contraction in extended form**
  `∫⁻ x, ‖P_t f x‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ`
  (Tonelli: `∫⁻x∫⁻y K(x-y)‖f y‖ₑ = ∫⁻y ‖f y‖ₑ · ∫⁻x K(x-y)ₑ = ∫⁻y ‖f y‖ₑ · 1`);
* **integrability preservation**: `Integrable f → Integrable (P_t f)`, via integrability of the
  kernel-product on the product measure space and `Integrable.integral_prod_left`;
* the **L¹ contraction in real form** `∫ x, ‖P_t f x‖ ≤ ∫ y, ‖f y‖` for integrable `f`;
* **conservation of mass** `∫ x, P_t f x = ∫ y, f y` for integrable `f` (Fubini + mass one).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology ENNReal

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

set_option linter.unusedVariables false

/-! ## ENNReal-norm (enorm) algebra for the kernel -/

/-- Multiplicativity of the extended norm when the left factor is nonnegative. -/
theorem enorm_mul_of_nonneg_left {a b : ℝ} (ha : 0 ≤ a) : ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by
  rw [enorm_eq_ofReal_abs, enorm_eq_ofReal ha, enorm_eq_ofReal_abs, abs_mul]
  rw [ENNReal.ofReal_mul (abs_nonneg a)]
  rw [abs_of_nonneg ha]

/-- The extended norm of the reflected kernel section, integrated over the space variable, equals
`1`: `∫⁻ x, ‖gaussianKernel n t (x - y)‖ₑ = 1` for `t > 0`. -/
theorem lintegral_enorm_gaussianKernel_sub_left (n : ℕ) {t : ℝ} (ht : 0 < t)
    (y : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y)‖ₑ ∂volume = 1 := by
  have hnonneg : 0 ≤ᵐ[volume] fun x : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) :=
    Eventually.of_forall fun x => gaussianKernel_nonneg n ht.le (x - y)
  have hstep : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (gaussianKernel n t (x - y)) ∂volume
      = ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) ∂volume) := by
    exact (ofReal_integral_eq_lintegral_ofReal
      (f := fun x : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y))
      (integrable_gaussianKernel_sub_left n ht y) hnonneg).symm
  calc ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y)‖ₑ ∂volume
      = ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (gaussianKernel n t (x - y)) ∂volume := by
          refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
          exact enorm_eq_ofReal (gaussianKernel_nonneg n ht.le (x - y))
    _ = ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) ∂volume) :=
          hstep
    _ = ENNReal.ofReal 1 := by
          rw [integral_gaussianKernel_sub_left n ht y]
    _ = 1 := ENNReal.ofReal_one

/-! ## Pointwise bound of the operator norm by the kernel convolution -/

/-- **Pointwise extended-norm bound.** For every `x`, `‖P_t f x‖ₑ ≤ ∫⁻ y, ‖K(x,y,t) * f y‖ₑ`.
This is mathlib's unconditional `enorm_integral_le_lintegral_enorm`: in the integrable case it is
the triangle inequality `‖∫‖ ≤ ∫‖·‖`, in the non-integrable case the Bochner integral vanishes by
`integral_undef`. -/
theorem heatOperator_enorm_le_lintegral_enorm (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖heatOperator n t f x‖ₑ ≤ ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume := by
  unfold heatOperator
  exact enorm_integral_le_lintegral_enorm (fun y : EuclideanSpace ℝ (Fin n) =>
    gaussianKernel n t (x - y) * f y)

/-! ## The Tonelli step: the kernel-product integral is bounded by the L¹ norm -/

/-- The integrated extended norm of the kernel product `(x, y) ↦ K(x - y) * f y` is bounded by
`∫⁻ y, ‖f y‖ₑ`; the inner integral over `x` of the kernel is exactly `1` (mass one). -/
theorem lintegral_enorm_heatKernelProduct_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n),
        ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume ∂volume
      ≤ ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume := by
  -- a.e.-strong measurability of the uncurried integrand, needed for Tonelli
  have hF : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t (p.1 - p.2) * f p.2) (volume.prod volume) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((continuous_gaussianKernel n).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    · exact hfm.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hAEMeas : AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖gaussianKernel n t (p.1 - p.2) * f p.2‖ₑ) (volume.prod volume) :=
    (continuous_enorm.aemeasurable.comp_aemeasurable hF.aemeasurable)
  have hswap := lintegral_lintegral_swap (μ := volume) (ν := volume)
    (f := fun x y : EuclideanSpace ℝ (Fin n) => ‖gaussianKernel n t (x - y) * f y‖ₑ)
    hAEMeas
  have hinner : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume
        = ‖f y‖ₑ * ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y)‖ₑ ∂volume := by
    intro y
    calc ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume
        = ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y)‖ₑ * ‖f y‖ₑ ∂volume := by
            refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
            exact enorm_mul_of_nonneg_left (gaussianKernel_nonneg n ht.le (x - y))
      _ = ‖f y‖ₑ * ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y)‖ₑ ∂volume := by
            rw [show ∫⁻ x : EuclideanSpace ℝ (Fin n),
                ‖gaussianKernel n t (x - y)‖ₑ * ‖f y‖ₑ ∂volume
                = ∫⁻ x : EuclideanSpace ℝ (Fin n),
                    ‖f y‖ₑ * ‖gaussianKernel n t (x - y)‖ₑ ∂volume by
              refine lintegral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)]
            rw [lintegral_const_mul (‖f y‖ₑ)
              (f := fun x : EuclideanSpace ℝ (Fin n) => ‖gaussianKernel n t (x - y)‖ₑ)
              (continuous_enorm.comp ((continuous_gaussianKernel n).comp
                (continuous_id.sub continuous_const))).measurable]
  calc ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume ∂volume
      = ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume ∂volume :=
        hswap
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ‖f y‖ₑ * ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y)‖ₑ ∂volume ∂volume := by
        refine lintegral_congr_ae (Eventually.of_forall hinner)
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ * 1 ∂volume := by
        refine lintegral_congr_ae (Eventually.of_forall fun y => ?_)
        change ‖f y‖ₑ * ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ‖gaussianKernel n t (x - y)‖ₑ ∂volume = ‖f y‖ₑ * 1
        rw [lintegral_enorm_gaussianKernel_sub_left n ht y]
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume := by
        refine lintegral_congr_ae (Eventually.of_forall fun y => mul_one _)
  exact le_rfl

/-! ## L¹ contraction (extended form) -/

/-- **L¹ contraction, extended form.** For `t > 0` and a.e.-strongly-measurable `f`,
`∫⁻ x, ‖P_t f x‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ`. -/
theorem heatOperator_lintegral_enorm_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfm : AEStronglyMeasurable f volume) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖heatOperator n t f x‖ₑ ∂volume
      ≤ ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume := by
  calc ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖heatOperator n t f x‖ₑ ∂volume
      ≤ ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume ∂volume := by
          refine lintegral_mono_ae (Eventually.of_forall fun x => ?_)
          exact heatOperator_enorm_le_lintegral_enorm n ht x
    _ ≤ ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume :=
          lintegral_enorm_heatKernelProduct_le n ht hfm

/-! ## Integrability preservation -/

/-- The kernel product `(x, y) ↦ K(x - y) * f y` is integrable on the product space whenever
`f` is integrable. -/
theorem heatKernelProduct_integrable (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume) :
    Integrable (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n t (x - y) * f y)) (volume.prod volume) := by
  have hF : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t (p.1 - p.2) * f p.2) (volume.prod volume) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((continuous_gaussianKernel n).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    · exact hfi.aestronglyMeasurable.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hAEMeas : AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖gaussianKernel n t (p.1 - p.2) * f p.2‖ₑ) (volume.prod volume) :=
    (continuous_enorm.aemeasurable.comp_aemeasurable hF.aemeasurable)
  refine ⟨hF, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt ?_ (hasFiniteIntegral_iff_enorm.mp hfi.hasFiniteIntegral)
  calc ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ‖gaussianKernel n t (p.1 - p.2) * f p.2‖ₑ ∂volume.prod volume
      = ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n t (x - y) * f y‖ₑ ∂volume ∂volume := by
          rw [lintegral_prod (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖gaussianKernel n t (p.1 - p.2) * f p.2‖ₑ) hAEMeas]
    _ ≤ ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume :=
          lintegral_enorm_heatKernelProduct_le n ht hfi.aestronglyMeasurable

/-- **Integrability preservation.** For `t > 0`, the heat operator maps integrable functions to
integrable functions. -/
theorem heatOperator_integrable (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume) :
    Integrable (heatOperator n t f) volume :=
  (heatKernelProduct_integrable n ht hfi).integral_prod_left

/-! ## L¹ contraction (real form) and mass conservation -/

/-- **L¹ contraction, real form.** For `t > 0` and integrable `f`, `∫ x, ‖P_t f x‖ ≤ ∫ y, ‖f y‖`. -/
theorem heatOperator_integral_norm_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume) :
    ∫ x : EuclideanSpace ℝ (Fin n), ‖heatOperator n t f x‖ ∂volume
      ≤ ∫ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ∂volume := by
  have hP : Integrable (heatOperator n t f) volume := heatOperator_integrable n ht hfi
  have hlenorm := heatOperator_lintegral_enorm_le n ht hfi.aestronglyMeasurable
  have hltf : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume < ⊤ :=
    hasFiniteIntegral_iff_enorm.mp hfi.hasFiniteIntegral
  have htoReal := ENNReal.toReal_mono (ne_top_of_lt hltf) hlenorm
  have hleft : ∫ x : EuclideanSpace ℝ (Fin n), ‖heatOperator n t f x‖ ∂volume
      = (∫⁻ x : EuclideanSpace ℝ (Fin n), ‖heatOperator n t f x‖ₑ ∂volume).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : EuclideanSpace ℝ (Fin n) =>
        ‖heatOperator n t f x‖)
      (Eventually.of_forall fun x => norm_nonneg _) hP.aestronglyMeasurable.norm]
    congr 1
    refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
    change ENNReal.ofReal ‖heatOperator n t f x‖ = ‖heatOperator n t f x‖ₑ
    rw [enorm_eq_ofReal_abs, Real.norm_eq_abs]
  have hright : ∫ y : EuclideanSpace ℝ (Fin n), ‖f y‖ ∂volume
      = (∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y : EuclideanSpace ℝ (Fin n) => ‖f y‖)
      (Eventually.of_forall fun y => norm_nonneg _) hfi.aestronglyMeasurable.norm]
    congr 1
    refine lintegral_congr_ae (Eventually.of_forall fun y => ?_)
    change ENNReal.ofReal ‖f y‖ = ‖f y‖ₑ
    rw [enorm_eq_ofReal_abs, Real.norm_eq_abs]
  rw [hleft, hright]
  exact htoReal

/-- **Conservation of mass.** For `t > 0` and integrable `f`, `∫ x, P_t f x = ∫ y, f y`. -/
theorem heatOperator_integral_eq_integral (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : Integrable f volume) :
    ∫ x : EuclideanSpace ℝ (Fin n), heatOperator n t f x ∂volume
      = ∫ y : EuclideanSpace ℝ (Fin n), f y ∂volume := by
  have hswap := integral_integral_swap (μ := volume) (ν := volume)
    (f := fun x y : EuclideanSpace ℝ (Fin n) => gaussianKernel n t (x - y) * f y)
    (heatKernelProduct_integrable n ht hfi)
  calc ∫ x : EuclideanSpace ℝ (Fin n), heatOperator n t f x ∂volume
      = ∫ x : EuclideanSpace ℝ (Fin n),
          ∫ y : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y ∂volume ∂volume := by
          unfold heatOperator
          rfl
    _ = ∫ y : EuclideanSpace ℝ (Fin n),
          ∫ x : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y ∂volume ∂volume :=
          hswap
    _ = ∫ y : EuclideanSpace ℝ (Fin n), f y ∂volume := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        calc ∫ x : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) * f y ∂volume
            = ∫ x : EuclideanSpace ℝ (Fin n), f y * gaussianKernel n t (x - y) ∂volume :=
              integral_congr_ae (Eventually.of_forall fun x => by ring)
          _ = f y * ∫ x : EuclideanSpace ℝ (Fin n), gaussianKernel n t (x - y) ∂volume :=
              integral_const_mul (f y) (fun x : EuclideanSpace ℝ (Fin n) =>
                gaussianKernel n t (x - y))
          _ = f y * 1 := by rw [integral_gaussianKernel_sub_left n ht y]
          _ = f y := mul_one _

end

end Poincare.D12.HeatSemigroup
