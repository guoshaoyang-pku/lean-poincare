/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.GeometricRepair

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.LaplacianSymmetryRefutation

**D13 heat-kernel bridge, companion note 5: the naive formal self-adjointness axiom is false for the
honest flat Laplacian.**

`GeometricRepair.lean` takes the constant-annihilation condition `Δ 1 = 0` as the one geometric
necessary condition that is soundly expressible over the schematic `HeatSpacetime` interface, and
states that the stronger classical condition — formal self-adjointness `∫ u · Δv = ∫ Δu · v`, stated
with the interface's Bochner integral over *all* functions — is not soundly stateable there. This
file turns that statement into a checked theorem for the honest one-dimensional flat operator (the
D11 packaged `laplacianLinearMap ℝ`):

* `flatLineSpacetime`: the honest flat spacetime on `ℝ` (Lebesgue volume, packaged Laplacian,
  Euclidean distance, dimension `1`);
* `hasDerivAt_tanh_real`, `tanh_eq_one_sub`, `tendsto_tanh_atTop_real`, `tendsto_tanh_atBot_real`:
  the calculus of `Real.tanh` used by the counterexample;
* `hasDerivAt_log_cosh`, `contDiff_log_cosh`, `laplacian_log_cosh`: the second-derivative identity
  `Δ (log ∘ cosh) = 1 - tanh²` for the packaged Laplacian;
* `integrable_one_sub_tanh_sq`, `integral_one_sub_tanh_sq`: `∫ x, (1 - tanh x ^ 2) = 2`, via the
  fundamental theorem of calculus on the whole real line;
* `not_forall_laplacian_symmetric_flatLine`: with `u = 1` (so `Δu = 0`) and `v = log ∘ cosh`, the
  left-hand side of the naive self-adjointness identity is `∫ (1 - tanh²) = 2` while the
  right-hand side is `∫ 0 · v = 0`; hence the all-functions Bochner-integral form of
  self-adjointness is **false** for the honest flat operator, and cannot be added as a field of a
  repaired schematic interface.

Consequence: the schematic interface cannot be repaired by adjoining the classical integration-by-
parts identities; the honest repair is the data-level `HeatKernelData` / `HeatKernelDataV1`
interface supplied by the bridge. All proofs are complete: no `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel

/-- Derivative of the real `tanh`: `(tanh)' = 1 - tanh²`. -/
theorem hasDerivAt_tanh_real (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hcs : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    rw [← Real.cosh_sq_sub_sinh_sq x]; ring
  have hval : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2
      = 1 - (Real.sinh x / Real.cosh x) ^ 2 := by
    rw [hcs]
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [hval] at h
  have htanh : Real.tanh = fun y : ℝ => Real.sinh y / Real.cosh y := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y
  rw [htanh]
  exact h

/-- `tanh x = 1 - 2 / (exp (2x) + 1)`. -/
theorem tanh_eq_one_sub (x : ℝ) :
    Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq]
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  have hnx : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hx : Real.exp x ≠ 0 := Real.exp_ne_zero x
  rw [h2, hnx]
  field_simp
  ring

/-- `tanh x → 1` at `+∞`. -/
theorem tendsto_tanh_atTop_real : Tendsto Real.tanh atTop (𝓝 1) := by
  rw [show Real.tanh = fun x : ℝ => 1 - 2 / (Real.exp (2 * x) + 1) from
    funext fun x => tanh_eq_one_sub x]
  have hden : Tendsto (fun x : ℝ => Real.exp (2 * x) + 1) atTop atTop := by
    have h2 : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact (Real.tendsto_exp_atTop.comp h2).atTop_add tendsto_const_nhds
  have h0 : Tendsto (fun x : ℝ => 2 / (Real.exp (2 * x) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  simpa using tendsto_const_nhds.sub h0

/-- `tanh x → -1` at `-∞`. -/
theorem tendsto_tanh_atBot_real : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  rw [show Real.tanh = fun x : ℝ => -Real.tanh (-x) from
    funext fun x => by rw [Real.tanh_neg, neg_neg]]
  have := tendsto_tanh_atTop_real.comp tendsto_neg_atBot_atTop
  simpa using this.neg

/-- The honest 1-dimensional flat spacetime with the D11 packaged Laplacian. -/
noncomputable def flatLineSpacetime : HeatSpacetime ℝ where
  volume := volume
  laplacian := laplacianLinearMap ℝ
  timeDerivative := 0
  dist := fun x y => |x - y|
  dim := 1

theorem hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cosh y)) (Real.tanh x) x := by
  have h := (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))
  simpa [Real.tanh_eq_sinh_div_cosh] using h

theorem contDiff_log_cosh : ContDiff ℝ 2 (fun x : ℝ => Real.log (Real.cosh x)) :=
  Real.contDiff_cosh.log (fun x => ne_of_gt (Real.cosh_pos x))

theorem laplacian_log_cosh :
    (laplacianLinearMap ℝ) (fun x : ℝ => Real.log (Real.cosh x)) =
      fun x => 1 - Real.tanh x ^ 2 := by
  rw [laplacianLinearMap_apply_of_contDiff contDiff_log_cosh]
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedDeriv_real]
  have h2 : iteratedDeriv 2 (fun y : ℝ => Real.log (Real.cosh y)) =
      deriv (deriv (fun y : ℝ => Real.log (Real.cosh y))) := by
    change iteratedDeriv (1 + 1) (fun y : ℝ => Real.log (Real.cosh y)) = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  have hderiv1 : deriv (fun y : ℝ => Real.log (Real.cosh y)) = Real.tanh :=
    funext fun y => (hasDerivAt_log_cosh y).deriv
  rw [hderiv1]
  exact (hasDerivAt_tanh_real x).deriv

theorem integrable_one_sub_tanh_sq : Integrable (fun x : ℝ => 1 - Real.tanh x ^ 2) := by
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ 1 - Real.tanh x ^ 2 := by
    intro x _
    have := Real.tanh_sq_lt_one x
    linarith
  have hIoi : IntegrableOn (fun x : ℝ => 1 - Real.tanh x ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_tanh_real x) hpos
      tendsto_tanh_atTop_real
  have hneg : ∀ x, HasDerivAt (fun y : ℝ => Real.tanh (-y))
      (-(1 - Real.tanh (-x) ^ 2)) x := by
    intro x
    have h := (hasDerivAt_tanh_real (-x)).comp x (hasDerivAt_neg x)
    have hval : (1 - Real.tanh (-x) ^ 2) * (-1) = -(1 - Real.tanh (-x) ^ 2) := by ring
    rw [hval] at h
    exact h
  have hnegneg : ∀ x ∈ Set.Ioi (0 : ℝ), -(1 - Real.tanh (-x) ^ 2) ≤ 0 := by
    intro x _
    have := Real.tanh_sq_lt_one (-x)
    linarith
  have hbot : Tendsto (fun x : ℝ => Real.tanh (-x)) atTop (𝓝 (-1)) :=
    tendsto_tanh_atBot_real.comp tendsto_neg_atTop_atBot
  have hIoi' : IntegrableOn (fun x : ℝ => -(1 - Real.tanh (-x) ^ 2)) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonpos' (fun x _ => hneg x) hnegneg hbot
  have hIoi'' : IntegrableOn (fun x : ℝ => 1 - Real.tanh (-x) ^ 2) (Set.Ioi 0) := by
    simpa only [Pi.neg_def, neg_neg] using hIoi'.neg
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have key : IntegrableOn (fun x : ℝ => 1 - Real.tanh x ^ 2) (Set.Iio 0) ↔
      IntegrableOn (fun x : ℝ => 1 - Real.tanh (-x) ^ 2) (Set.Ioi 0) := by
    have h := hemb.integrableOn_map_iff (f := fun x : ℝ => 1 - Real.tanh x ^ 2)
      (μ := (volume : Measure ℝ)) (s := Set.Iio 0)
    rw [Measure.map_neg_eq_self] at h
    simpa only [Function.comp_def, Set.neg_preimage, Set.neg_Iio, neg_zero] using h
  have hIio : IntegrableOn (fun x : ℝ => 1 - Real.tanh x ^ 2) (Set.Iio 0) := key.mpr hIoi''
  have hIic : IntegrableOn (fun x : ℝ => 1 - Real.tanh x ^ 2) (Set.Iic 0) := by
    have hunion : Set.Iic (0 : ℝ) = Set.Iio 0 ∪ {0} := by
      ext x
      simp [le_iff_lt_or_eq]
    rw [hunion]
    exact hIio.union (integrableOn_singleton (f := fun x : ℝ => 1 - Real.tanh x ^ 2)
      (x := 0) (hx := by simp))
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

theorem integral_one_sub_tanh_sq : ∫ x : ℝ, (1 - Real.tanh x ^ 2) = 2 := by
  have := integral_of_hasDerivAt_of_tendsto (f := Real.tanh)
    (f' := fun x : ℝ => 1 - Real.tanh x ^ 2) (m := -1) (n := 1)
    (fun x => hasDerivAt_tanh_real x) integrable_one_sub_tanh_sq
    tendsto_tanh_atBot_real tendsto_tanh_atTop_real
  rw [show (1 : ℝ) - (-1) = 2 by norm_num] at this
  exact this

/-- **The naive formal self-adjointness axiom is FALSE for the honest 1-dimensional flat
Laplacian.** -/
theorem not_forall_laplacian_symmetric_flatLine :
    ¬ (∀ u v : ℝ → ℝ,
        (∫ x, u x * flatLineSpacetime.laplacian v x ∂flatLineSpacetime.volume) =
          ∫ x, flatLineSpacetime.laplacian u x * v x ∂flatLineSpacetime.volume) := by
  intro hsym
  have h1 : flatLineSpacetime.laplacian (1 : ℝ → ℝ) = 0 := by
    show (laplacianLinearMap ℝ) (1 : ℝ → ℝ) = 0
    have hone : (fun _ : ℝ => (1 : ℝ)) = 1 := rfl
    rw [← hone, laplacianLinearMap_apply_of_contDiff
      (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)))]
    exact InnerProductSpace.laplacian_const
  have hv : flatLineSpacetime.laplacian (fun x : ℝ => Real.log (Real.cosh x)) =
      fun x => 1 - Real.tanh x ^ 2 := laplacian_log_cosh
  have key := hsym (1 : ℝ → ℝ) (fun x : ℝ => Real.log (Real.cosh x))
  rw [hv, h1] at key
  have hvol : flatLineSpacetime.volume = (volume : Measure ℝ) := rfl
  rw [hvol] at key
  simp only [Pi.one_apply, one_mul, Pi.zero_apply, zero_mul, integral_zero] at key
  have h2 := integral_one_sub_tanh_sq
  linarith

end Poincare.D13.HeatKernelBridge
