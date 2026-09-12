/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.L1Contraction
import Poincare.D12.HeatSemigroup.LinfContraction

/-!
# Poincare.D12.HeatSemigroup.Example

**D12 heat-semigroup analysis, part 7: a concrete nondegenerate example.**

The Gaussian at time `s` centred at `a`, `f y = gaussianKernel n s (y - a)`, is a strictly
positive, bounded, integrable function. Under the heat operator it evolves exactly as

`P_t f x = gaussianKernel n (t + s) (x - a)`,

proved from the D10 convolution identity. This example checks non-vacuity of the D12 estimates:

* the image is strictly positive everywhere (positivity, with a witness);
* the total mass is preserved (`∫ P_t f = 1`, matching the L¹ analysis);
* the L∞ contraction applies with the explicit constant `(4πs)^{-n/2}`;
* the L¹ contraction applies with both sides equal to `1`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology BoundedContinuousFunction

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

set_option linter.unusedVariables false

/-- **The heat operator reproduces Gaussians at later time.** For `s, t > 0` and any centre `a`,
`P_t (gaussianKernel n s (· - a)) = gaussianKernel n (t + s) (· - a)`, from the D10 convolution
identity. -/
theorem heatOperator_gaussianKernel (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (a x : EuclideanSpace ℝ (Fin n)) :
    heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x
      = gaussianKernel n (t + s) (x - a) := by
  unfold heatOperator
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) =>
      gaussianKernel n t (x - y) * gaussianKernel n s (y - a))
      = fun y => (fun z : EuclideanSpace ℝ (Fin n) =>
        gaussianKernel n t (x - a - z) * gaussianKernel n s z) (y - a) := by
    funext y
    rw [show x - y = x - a - (y - a) by abel]
  rw [hfun, integral_sub_right_eq_self (fun z : EuclideanSpace ℝ (Fin n) =>
    gaussianKernel n t (x - a - z) * gaussianKernel n s z) a]
  rw [show (∫ z : EuclideanSpace ℝ (Fin n),
      gaussianKernel n t (x - a - z) * gaussianKernel n s z)
      = ∫ z : EuclideanSpace ℝ (Fin n),
          gaussianKernel n s z * gaussianKernel n t (x - a - z) by
    refine integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)]
  rw [gaussianKernel_convolution n hs ht (x - a), add_comm s t]

/-- **Non-vacuity of positivity**: the image of the Gaussian is strictly positive everywhere. -/
theorem heatOperator_gaussianKernel_pos (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (a x : EuclideanSpace ℝ (Fin n)) :
    0 < heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x := by
  rw [heatOperator_gaussianKernel n hs ht a x]
  exact gaussianKernel_pos n (add_pos ht hs) (x - a)

/-- **Non-vacuity of mass preservation**: the Gaussian example has total mass one at every time. -/
theorem heatOperator_gaussianKernel_integral (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (a : EuclideanSpace ℝ (Fin n)) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x = 1 := by
  rw [heatOperator_integral_eq_integral n ht
    ((integrable_of_integral_eq_one (gaussianKernel_integral n hs)).comp_sub_right a)]
  rw [integral_sub_right_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n s z) a]
  exact gaussianKernel_integral n hs

/-- **Non-vacuity of the L∞ contraction**: the Gaussian example is bounded by its prefactor and
the heat operator preserves that bound. -/
theorem heatOperator_gaussianKernel_norm_le (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (a x : EuclideanSpace ℝ (Fin n)) :
    ‖heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x‖
      ≤ (4 * π * s) ^ (-(n : ℝ) / 2) := by
  have hM : (0 : ℝ) ≤ (4 * π * s) ^ (-(n : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  refine heatOperator_norm_le_of_forall_norm_le n ht hM ?_ x
  intro y
  rw [Real.norm_of_nonneg (gaussianKernel_nonneg n hs.le (y - a))]
  exact gaussianKernel_sub_le_prefactor n hs y a

/-- **Non-vacuity of the L¹ contraction**: both sides of the L¹ estimate equal `1` on the
Gaussian example. -/
theorem heatOperator_gaussianKernel_L1 (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (a : EuclideanSpace ℝ (Fin n)) :
    (∫ x : EuclideanSpace ℝ (Fin n),
        ‖heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x‖,
      ∫ y : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n s (y - a)‖) = (1, 1) := by
  apply Prod.ext
  · change ∫ x : EuclideanSpace ℝ (Fin n),
      ‖heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) x‖ = 1
    have hf : Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussianKernel n s (y - a)) volume :=
      (integrable_of_integral_eq_one (gaussianKernel_integral n hs)).comp_sub_right a
    have hP := heatOperator_integrable n ht hf
    rw [integral_congr_ae (Eventually.of_forall fun x => by
      rw [heatOperator_gaussianKernel n hs ht a x, Real.norm_of_nonneg
        (gaussianKernel_nonneg n (add_pos ht hs).le (x - a))])]
    rw [integral_sub_right_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n (t + s) z) a]
    exact gaussianKernel_integral n (add_pos ht hs)
  · change ∫ y : EuclideanSpace ℝ (Fin n), ‖gaussianKernel n s (y - a)‖ = 1
    rw [integral_congr_ae (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (gaussianKernel_nonneg n hs.le (y - a))])]
    rw [integral_sub_right_eq_self (fun z : EuclideanSpace ℝ (Fin n) => gaussianKernel n s z) a]
    exact gaussianKernel_integral n hs

end

end Poincare.D12.HeatSemigroup
