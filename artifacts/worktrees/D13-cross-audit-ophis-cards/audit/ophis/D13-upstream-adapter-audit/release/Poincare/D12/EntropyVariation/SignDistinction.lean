/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-entropy-variation)

# Sign distinction: increasing Perelman `F` vs the nonincreasing toy functionals; the shrinker `W` identity

This module states the two proved monotonicity facts **side by side**, so the
convention mismatch is resolved by construction rather than by renaming:

1. **Perelman's `F` along the `F`-flow is strictly increasing.**  On the flat
   Gaussian model of `FFlowModel` (`∂ₜg = -2(Ric + ∇²f)`, measure fixed), the
   derivative is `dF/dt = n/(2(τ₀-t)²) > 0` (`fflow_F_hasDerivAt_closedForm`,
   `fflow_F_deriv_pos`) and `F` is strictly increasing on the geometric domain
   (`fflow_F_strictMonoOn`).  This is the correct sign for the D7
   `FDerivativeStatement` convention `derivative = +FDissipation`.

2. **The old toy functional is nonincreasing.**  The D2/D4 finite reaction model
   `perelmanF c lam = ∑ i, (c i + lam i²) e^{-lam i}` along the D2 reaction ODE is
   nonincreasing (`perelmanF_antitone`), and the D2 heat-grid ℓ² energy is
   nonincreasing in discrete time (`HeatGridEvolution.energy_antitone`).  These
   are *different objects* on *different state spaces* (finite sums over a finite
   reaction network, not the continuum integral `F = ∫(R+|∇f|²) dm`): the sign
   difference is real and is documented here with full types.

3. **The shrinker `W`-derivative identity.**  On the Gaussian shrinker
   (`shrinkerEntropyData`), Perelman's `dW/dτ = -2τ∫|Ric+∇²f - g/(2τ)|² dm` holds
   with **both sides computed independently**: the left side is the derivative of
   `τ ↦ W(τ)` which vanishes identically (`shrinkerEntropyData_W_value` ⇒
   `shrinkerWOfTau_hasDerivAt`), and the right side vanishes because the
   dissipation density is pointwise zero (`shrinker_w_dissipation_density_zero` ⇒
   `shrinkerWDissipationDensity_zero` ⇒ `shrinkerWDissipation_zero`), using
   `Ric = 0` (flat model) and the proved Hessian identity `∇²f = g/(2τ)`.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file.
-/
import Poincare.D12.EntropyVariation.FFlowModel
import Poincare.Longrun.Evolution
import Poincare.Longrun.Entropy.DiscreteHeat

open MeasureTheory Real Filter TopologicalSpace Metric Set
open scoped Topology Filter BigOperators InnerProductSpace RealInnerProductSpace
open Poincare.Longrun.Entropy
open Poincare.Longrun.Evolution
open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.PDE
open Poincare.D10.HeatKernelEuclidean

namespace Poincare.D12.EntropyVariation

noncomputable section

/-! ## Side by side: increasing Perelman `F` vs nonincreasing toy functionals -/

/-- **The sign distinction, side by side (monotonicity form).**

* (increasing, continuum) Perelman's `F` along the `F`-flow on the flat Gaussian
  model: for `n ≥ 1` and `s < t < τ₀`, `F(E s) < F(E t)` — proved in `FFlowModel`;
* (nonincreasing, discrete toy) the D2/D4 finite Perelman-type functional along
  any D2 reaction-ODE solution on `[0,T]` with `1 ≤ c`: `perelmanF c (traj t) ≤
  perelmanF c (traj s)` for `s ≤ t` — the upstream theorem `perelmanF_antitone`.

The two functionals live on different state spaces (a continuum Gaussian model
with a genuine integral `∫(R+|∇f|²) dm` versus a finite sum over a reaction
network); the sign difference is not a convention clash inside one object. -/
theorem perelmanFFlow_increasing_toy_nonincreasing
    {n : ℕ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hn : 0 < n)
    {ι : Type*} [Fintype ι] (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    (∀ s t : ℝ, s < t → t < τ₀ →
      (fflowEntropyData n τ₀ hτ₀ s).F < (fflowEntropyData n τ₀ hτ₀ t).F) ∧
    (∀ ⦃s t : ℝ⦄, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
      perelmanF c (traj t) ≤ perelmanF c (traj s)) := by
  constructor
  · intro s t hst ht
    have hmono := fflow_F_strictMonoOn n τ₀ hτ₀ hn
    exact hmono (show s ∈ Iio τ₀ from lt_trans hst ht) ht hst
  · intro s t hs ht hst
    exact perelmanF_antitone F hc ev hs ht hst

/-- **The sign distinction, side by side (derivative form).**

* (continuum) `HasDerivAt (fun u => F(E u)) (n/(2(τ₀-t)²)) t` with
  `n/(2(τ₀-t)²) > 0` — the derivative of Perelman's `F` along the `F`-flow is
  positive (F increasing);
* (discrete toy) the D2/D4 right derivative of `perelmanF` along the reaction ODE
  equals the negative Gibbs-weighted sum and is `≤ 0` (toy nonincreasing). -/
theorem derivative_sign_distinction
    {n : ℕ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hn : 0 < n)
    {ι : Type*} [Fintype ι] (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj)
    {t : ℝ} (ht : t < τ₀) (ht' : t ∈ Ico 0 T) :
    HasDerivAt (fun u => (fflowEntropyData n τ₀ hτ₀ u).F) ((n : ℝ) / (2 * (τ₀ - t) ^ 2)) t ∧
      0 < (n : ℝ) / (2 * (τ₀ - t) ^ 2) ∧
      HasDerivWithinAt (fun s => perelmanF c (traj s))
        (-∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) * Real.exp (-(traj t i)))
        (Ici t) t ∧
      (-∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) * Real.exp (-(traj t i))) ≤ 0 := by
  constructor
  · exact fflow_F_hasDerivAt_closedForm n τ₀ hτ₀ ht
  constructor
  · exact fflow_F_deriv_pos n τ₀ hτ₀ hn ht
  constructor
  · exact hasDerivWithinAt_perelmanF F c ev ht'
  · exact perelmanF_dissipation_nonpos F hc (traj t)

/-- **The D2 heat-grid ℓ² energy is nonincreasing in discrete time** (the second
toy object; upstream `HeatGridEvolution.energy_antitone`), under the explicit
CFL/convexity condition `0 ≤ α ≤ 1/2`.  This is a finite-grid energy, again a
different object from the continuum Perelman `F`. -/
theorem toy_heatEnergy_nonincreasing {N : ℕ} {α : ℝ} (evg : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    Antitone fun t : ℕ => energy (evg.u t) N :=
  evg.energy_antitone hα0 hα1

/-! ## The shrinker `W`-derivative identity: both sides computed independently -/

/-- The `W`-functional of the shrinker as a function of the time-scale `τ`
(defined as `0` outside `τ > 0`; the claims below are all for `τ > 0`). -/
noncomputable def shrinkerWOfTau (n : ℕ) (τ : ℝ) : ℝ :=
  if h : 0 < τ then EntropyData.W (shrinkerEntropyData n τ h) else 0

/-- `W(τ) = 0` for every `τ > 0` (Perelman's shrinker equality case). -/
theorem shrinkerWOfTau_eq_zero (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    shrinkerWOfTau n τ = 0 := by
  unfold shrinkerWOfTau
  simp [hτ, shrinkerEntropyData_W_value n τ hτ]

/-- **Left side of the `W` identity**: `dW/dτ = 0` on the shrinker, obtained from
the proved identity `W(τ) ≡ 0` (the function is locally constant, so its
derivative is zero — no assumption about the derivative of `W` is made). -/
theorem shrinkerWOfTau_hasDerivAt (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun u => shrinkerWOfTau n u) (0 : ℝ) τ := by
  have hev : (fun u => shrinkerWOfTau n u) =ᶠ[𝓝 τ] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [ball_mem_nhds τ (by positivity : 0 < τ / 2)] with u hu
    have hu' : 0 < u := by
      have hmem := mem_ball.mp hu
      have habs : |u - τ| < τ / 2 := by simpa [dist_eq_norm] using hmem
      have : τ - τ / 2 < u := by
        have := (abs_lt.mp habs).1
        linarith
      linarith [show τ - τ / 2 = τ / 2 by field_simp; ring]
    rw [shrinkerWOfTau_eq_zero n hu']
  exact (hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq hev

/-- The `W`-dissipation density `|Ric + ∇²f - g/(2τ)|²` on the shrinker, written
in the standard orthonormal basis of `ℝⁿ` (`Ric = 0` is the flat-model datum). -/
noncomputable def shrinkerWDissipationDensity (n : ℕ) (τ : ℝ) (x : Euc n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((iteratedFDeriv ℝ 2 (shrinkerFpot τ) x ![EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ j])
      - (1 / (2 * τ)) * ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ j⟫_ℝ) ^ 2

/-- **Right side of the `W` identity, pointwise**: the dissipation density
vanishes identically, because `Ric = 0` and `∇²f = g/(2τ)` (the proved Hessian
identity `shrinker_w_dissipation_density_zero`). -/
theorem shrinkerWDissipationDensity_zero (n : ℕ) (τ : ℝ) (hτ : τ ≠ 0) (x : Euc n) :
    shrinkerWDissipationDensity n τ x = 0 := by
  unfold shrinkerWDissipationDensity
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  change (iteratedFDeriv ℝ 2 (shrinkerFpot τ) x
      ![EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ j]
      - (1 / (2 * τ)) * ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        EuclideanSpace.basisFun (Fin n) ℝ j⟫_ℝ) ^ 2 = 0
  have hzero := shrinker_w_dissipation_density_zero τ hτ x
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  rw [hzero]
  norm_num

/-- Integrability of the dissipation integrand (it is pointwise zero). -/
theorem integrable_shrinkerWDissipationDensity_mul (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun x : Euc n => shrinkerWDissipationDensity n τ x * gaussianKernel n τ x) := by
  have hzero : (fun x : Euc n => shrinkerWDissipationDensity n τ x * gaussianKernel n τ x)
      = fun _ : Euc n => (0 : ℝ) := by
    funext x
    rw [shrinkerWDissipationDensity_zero n τ (ne_of_gt hτ) x]
    simp
  rw [hzero]
  simp

/-- The `W`-dissipation integral `-2τ ∫ |Ric+∇²f-g/(2τ)|² dm` of the shrinker. -/
noncomputable def shrinkerWDissipation (n : ℕ) (τ : ℝ) : ℝ :=
  -2 * τ * ∫ x : Euc n, shrinkerWDissipationDensity n τ x * gaussianKernel n τ x

/-- The dissipation integral vanishes: `-2τ ∫ |Ric+∇²f-g/(2τ)|² dm = 0`. -/
theorem shrinkerWDissipation_zero (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    shrinkerWDissipation n τ = 0 := by
  unfold shrinkerWDissipation
  have hfun : (fun x : Euc n => shrinkerWDissipationDensity n τ x * gaussianKernel n τ x)
      =ᵐ[volume] fun _ : Euc n => (0 : ℝ) := by
    filter_upwards with x
    rw [shrinkerWDissipationDensity_zero n τ (ne_of_gt hτ) x]
    simp
  rw [integral_congr_ae hfun]
  rw [MeasureTheory.integral_zero]
  ring

/-- **The shrinker `W`-derivative identity, with both sides computed
independently.**  Perelman's identity `dW/dτ = -2τ ∫ |Ric+∇²f - g/(2τ)|² dm`
holds on the Gaussian shrinker: the left side is the derivative of `τ ↦ W(τ)`
(proved to be `0` from `W ≡ 0`), and the right side `shrinkerWDissipation n τ`
is proved to be `0` from the pointwise vanishing of the density.  `Ric = 0` is
the flat-model datum and `∇²f = g/(2τ)` is the proved Hessian identity, so this
is Perelman's equality case of `W`-monotonicity, computed, not assumed. -/
theorem shrinker_W_derivative_identity (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun u => shrinkerWOfTau n u) (shrinkerWDissipation n τ) τ := by
  rw [shrinkerWDissipation_zero n hτ]
  exact shrinkerWOfTau_hasDerivAt n τ hτ

end

end Poincare.D12.EntropyVariation
