/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.Smoothing
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Poincare.D12.HeatSemigroup.LinfContraction

**D12 heat-semigroup analysis, part 4: L∞ contraction on the Banach space of bounded continuous
functions.**

Let `E = EuclideanSpace ℝ (Fin n)`. For `t > 0` the heat operator `P_t` restricts to a map
`heatOperatorBCF n t : (E →ᵇ ℝ) → (E →ᵇ ℝ)`: continuity of `x ↦ P_t f x` is the smoothing lemma
`continuous_heatOperator` (part 3), and boundedness follows from the pointwise L∞ estimate
(part 1) with `M = ‖f‖`, the sup norm of the bounded continuous function `f`.

The main theorem is the genuine Banach-space contraction

`‖heatOperatorBCF n t f‖ ≤ ‖f‖`

for the sup norm of `E →ᵇ ℝ`, for every `t > 0` and every bounded continuous `f`, using
Lebesgue measure and the explicit Gaussian kernel.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology BoundedContinuousFunction

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

set_option linter.unusedVariables false

/-- **The heat operator as an endomorphism of bounded continuous functions.** For `t > 0`,
`P_t f` is continuous (smoothing lemma) and bounded by `‖f‖` pointwise (L∞ estimate), so it is a
bounded continuous function again. -/
def heatOperatorBCF (n : ℕ) {t : ℝ} (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) : EuclideanSpace ℝ (Fin n) →ᵇ ℝ :=
  { toFun := fun x => heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => f y) x
    continuous_toFun := by
      have hM : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
      exact continuous_heatOperator n ht f.continuous.aestronglyMeasurable hM
        (fun y : EuclideanSpace ℝ (Fin n) => f.norm_coe_le_norm y)
    map_bounded' := by
      refine ⟨2 * ‖f‖, fun x y => ?_⟩
      calc dist (heatOperator n t (fun z : EuclideanSpace ℝ (Fin n) => f z) x)
            (heatOperator n t (fun z : EuclideanSpace ℝ (Fin n) => f z) y)
          = ‖heatOperator n t (fun z : EuclideanSpace ℝ (Fin n) => f z) x -
              heatOperator n t (fun z : EuclideanSpace ℝ (Fin n) => f z) y‖ := rfl
        _ ≤ ‖heatOperator n t (fun z : EuclideanSpace ℝ (Fin n) => f z) x‖ +
              ‖heatOperator n t (fun z : EuclideanSpace ℝ (Fin n) => f z) y‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := by
              have hM : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
              gcongr
              · exact heatOperator_norm_le_of_forall_norm_le n ht hM
                  (fun z : EuclideanSpace ℝ (Fin n) => f.norm_coe_le_norm z) x
              · exact heatOperator_norm_le_of_forall_norm_le n ht hM
                  (fun z : EuclideanSpace ℝ (Fin n) => f.norm_coe_le_norm z) y
        _ = 2 * ‖f‖ := by ring }

/-- The bounded-continuous heat operator evaluated at a point is the heat operator. -/
@[simp]
theorem heatOperatorBCF_apply (n : ℕ) {t : ℝ} (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    heatOperatorBCF n ht f x = heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => f y) x :=
  rfl

/-- **L∞ contraction.** For every `t > 0` the heat operator is a contraction (norm `≤ 1`) on the
Banach space `EuclideanSpace ℝ (Fin n) →ᵇ ℝ` of bounded continuous functions with the sup norm,
against Lebesgue measure and the explicit Gaussian kernel: `‖P_t f‖ ≤ ‖f‖`. -/
theorem heatOperatorBCF_norm_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) :
    ‖heatOperatorBCF n ht f‖ ≤ ‖f‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
  intro x
  have hM : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  simpa [heatOperatorBCF_apply] using
    heatOperator_norm_le_of_forall_norm_le n ht hM
      (fun y : EuclideanSpace ℝ (Fin n) => f.norm_coe_le_norm y) x

end

end Poincare.D12.HeatSemigroup
