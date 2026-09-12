/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.Basic
import Poincare.D11.HeatKernelBridge.InitialCondition
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Poincare.D12.HeatSemigroup.StrongContinuity

**D12 heat-semigroup analysis, part 5: strong continuity at time zero.**

The heat semigroup `t ↦ P_t` is strongly continuous at `t = 0` in the following precise sense,
proved here from the D11 weak initial condition `flatKernel_tendsto_integral` (which is the
approximation-of-identity theorem for the explicit Gaussian kernel) together with the
compatibility `heatOperator_eq_integral_flatKernel`:

* **pointwise**: for every continuous integrable `f` and every `x`,
  `Tendsto (fun t => heatOperator n t f x) (𝓝[>] 0) (𝓝 (f x))`;
* **compactly supported form**: for every continuous compactly supported `f`;
* **uniform on compact sets is NOT claimed** (the D11 input is pointwise; it is recorded as a
  follow-up obligation, not assumed).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Real Filter
open scoped Topology BoundedContinuousFunction

namespace Poincare.D12.HeatSemigroup

noncomputable section

open Poincare.D10.HeatKernelEuclidean
open Poincare.D11.HeatKernelBridge

set_option linter.unusedVariables false

/-- **Strong continuity at `0`, pointwise.** For continuous integrable `f` the heat operator
reproduces `f` pointwise as `t → 0⁺`, for every `t > 0`-valued approach: this is exactly the D11
weak initial condition for the explicit Euclidean kernel, transferred through the compatibility
`heatOperator_eq_integral_flatKernel`. -/
theorem heatOperator_tendsto_nhdsGT_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (hfi : Integrable f volume) :
    Tendsto (fun t : ℝ => heatOperator n t f x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have h := flatKernel_tendsto_integral n x hf hfi
  refine Tendsto.congr' ?_ h
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heatOperator_eq_integral_flatKernel n ht f x).symm

/-- **Strong continuity at `0`, compactly supported test functions.** -/
theorem heatOperator_tendsto_nhdsGT_zero_of_hasCompactSupport (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    Tendsto (fun t : ℝ => heatOperator n t f x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  exact heatOperator_tendsto_nhdsGT_zero n x hf (hf.integrable_of_hasCompactSupport hfs)

/-- **Strong continuity at `0` in the one-point convolution form.** -/
theorem heatOperator_tendsto_nhdsGT_zero_conv (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (hfi : Integrable f volume) :
    Tendsto (fun t : ℝ => ∫ z : EuclideanSpace ℝ (Fin n), gaussianKernel n t z * f (x - z))
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have h := heatOperator_tendsto_nhdsGT_zero n x hf hfi
  refine Tendsto.congr' ?_ h
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact heatOperator_eq_integral_sub n t f x

/-- **Explicit obligation (not claimed):** strong continuity at `0` for a general bounded
continuous (non-integrable) test function requires a dominated-convergence argument splitting
near/infinity mass; the D11 peak-function input applies only to integrable test functions. -/
def StrongContinuityBoundedContinuousObligation (n : ℕ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ),
    Tendsto (fun t : ℝ => heatOperator n t (fun y : EuclideanSpace ℝ (Fin n) => f y) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x))

end

end Poincare.D12.HeatSemigroup
