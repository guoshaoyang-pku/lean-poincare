/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (L3-analytic-critical-path)
-/

import Poincare.L3.HeatTimeDeriv.UniformBridge

/-!
# The heat semigroup as a differentiable `BCFn n`-valued curve

`UniformMildToClassicalBridge` (`UniformBridge.lean`) states the uniform-in-space convergence of
the time difference quotients of `s ↦ K_s * f`. This file packages that convergence into the
Banach-space statement that a downstream Duhamel argument consumes:

* `timeDerivBCF n ht f : BCFn n`, the kernel-derivative integral as a bounded continuous
  function (continuity by `continuous_of_dominated` with the `x`-independent domination
  `timeDerivBound n t 1`; boundedness by the same estimate);
* `hasDerivAt_heatConv_BCF : HasDerivAt (fun s => heatConv n s f.val) (timeDerivBCF n ht f) t`
  — the Gaussian heat semigroup is differentiable at every positive time as a curve in the
  Banach space of bounded uniformly continuous functions, with the expected derivative.

This is the strongest form of the D12 mild-to-classical bridge available at this layer: the
remaining classical-solution residual is the spatial second derivative
(`SpatialLaplacianBridge`) and the Leibniz rule for the Duhamel `F`-term.

Scope: Euclidean model theorem. No manifold heat kernel, no Ricci flow, no Poincaré statement.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.L3.HeatTimeDeriv

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatSemigroup
open Poincare.D12.ParabolicLocal

/-! ## Continuity and boundedness of the kernel-derivative integral -/

/-- **Continuity in the space variable.** `x ↦ ∫ z, g_t(z) f(x - z) dz` is continuous: dominated
convergence with the `x`-independent integrable domination `timeDerivBound n t 1`. -/
theorem continuous_timeDerivIntegral (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => timeDerivIntegral n t f.val x := by
  have htrans : (fun x : EuclideanSpace ℝ (Fin n) => timeDerivIntegral n t f.val x)
      = fun x => ∫ z : EuclideanSpace ℝ (Fin n), timeDerivKernel n t z * f.val (x - z) := by
    funext x
    exact timeDerivIntegral_eq_translate n t f.val x
  rw [htrans]
  refine continuous_of_dominated (μ := volume)
    (F := fun x (z : EuclideanSpace ℝ (Fin n)) => timeDerivKernel n t z * f.val (x - z))
    (bound := fun z : EuclideanSpace ℝ (Fin n) => timeDerivBound n t 1 z * ‖f.val‖)
    ?_ ?_ ?_ ?_
  · intro x
    exact ((continuous_timeDerivKernel n t).mul
      (f.val.continuous.comp (continuous_const.sub continuous_id))).measurable.aestronglyMeasurable
  · intro x
    filter_upwards with z
    rw [norm_mul]
    exact mul_le_mul (norm_timeDerivKernel_le_normalized_self n ht z)
      (BoundedContinuousFunction.norm_coe_le_norm f.val (x - z))
      (norm_nonneg _) (timeDerivBound_nonneg n ht zero_le_one z)
  · exact (integrable_timeDerivBound_one n ht).mul_const ‖f.val‖
  · filter_upwards with z
    have h1 : Continuous fun x : EuclideanSpace ℝ (Fin n) => f.val (x - z) :=
      f.val.continuous.comp (continuous_id.sub continuous_const)
    exact (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin n) =>
      timeDerivKernel n t z).mul h1

/-- **Boundedness of the kernel-derivative integral**, with the explicit bound
`‖f‖ · ∫ z, timeDerivBound n t 1 z`. -/
theorem norm_timeDerivIntegral_le (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖timeDerivIntegral n t f.val x‖ ≤
      ‖f.val‖ * ∫ z : EuclideanSpace ℝ (Fin n), timeDerivBound n t 1 z := by
  rw [timeDerivIntegral_eq_translate]
  calc ‖∫ z : EuclideanSpace ℝ (Fin n), timeDerivKernel n t z * f.val (x - z)‖
      ≤ ∫ z : EuclideanSpace ℝ (Fin n), ‖timeDerivKernel n t z * f.val (x - z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin n), timeDerivBound n t 1 z * ‖f.val‖ := by
        refine integral_mono ?_ ?_ ?_
        · exact (integrable_timeDerivKernel_mul n ht (u := t) ⟨by linarith, by linarith⟩
            f x).norm
        · exact (integrable_timeDerivBound_one n ht).mul_const ‖f.val‖
        · intro z
          beta_reduce
          rw [norm_mul]
          exact mul_le_mul (norm_timeDerivKernel_le_normalized_self n ht z)
            (BoundedContinuousFunction.norm_coe_le_norm f.val (x - z))
            (norm_nonneg _) (timeDerivBound_nonneg n ht zero_le_one z)
    _ = (∫ z : EuclideanSpace ℝ (Fin n), timeDerivBound n t 1 z) * ‖f.val‖ := by
        rw [integral_mul_const]
    _ = ‖f.val‖ * ∫ z : EuclideanSpace ℝ (Fin n), timeDerivBound n t 1 z := by ring

/-! ## The derivative as a bounded continuous function -/

/-- The time derivative of the heat-semigroup orbit as an element of `BCFn n`. -/
def timeDerivBCF (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n) : BCFn n :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => timeDerivIntegral n t f.val x)
    (continuous_timeDerivIntegral n ht f)
    (‖f.val‖ * ∫ z : EuclideanSpace ℝ (Fin n), timeDerivBound n t 1 z)
    (fun x => norm_timeDerivIntegral_le n ht f x)

/-- The underlying function of `timeDerivBCF` is the kernel-derivative integral. -/
@[simp]
theorem timeDerivBCF_apply (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n)
    (x : EuclideanSpace ℝ (Fin n)) :
    timeDerivBCF n ht f x = timeDerivIntegral n t f.val x := rfl

/-! ## The Banach-space derivative of the heat semigroup -/

/-- **The Gaussian heat semigroup is differentiable in the Banach space `BCFn n`.** For every
`t > 0` and every `BUC` datum `f`, the orbit `s ↦ K_s * f` has derivative `timeDerivBCF n ht f`
at `t`. This is the Banach-space form of the mild-to-classical bridge that a Duhamel argument
consumes. -/
theorem hasDerivAt_heatConv_BCF (n : ℕ) {t : ℝ} (ht : 0 < t) (f : BUCn n) :
    HasDerivAt (fun s : ℝ => heatConv n s f.val) (timeDerivBCF n ht f) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    uniformMildToClassicalBridge_holds n ht f (ε / 2) (by linarith)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with h hball hhne
  have hlt : |h| < δ := by simpa [Real.dist_eq] using hball
  have hne : h ≠ 0 := hhne
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖(h⁻¹ • (heatConv n (t + h) f.val - heatConv n t f.val) - timeDerivBCF n ht f) x‖
        < ε / 2 := by
    intro x
    have hx := hδ h (abs_pos.mpr hne) hlt x
    simpa [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, div_eq_inv_mul, Real.norm_eq_abs] using hx
  rw [dist_eq_norm]
  exact lt_of_le_of_lt
    ((BoundedContinuousFunction.norm_le (by linarith)).mpr fun x => le_of_lt (hpoint x))
    (by linarith)

end

end Poincare.L3.HeatTimeDeriv
