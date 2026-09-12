/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-entropy-variation)

# The F-flow model: exact derivative identity `dF/dt = 2∫|Ric+∇²f|² dm` on the shrinking flat Gaussian

## The model (exact geometric restrictions)

On `X = ℝⁿ` with the *flat* metric (`Ric = 0`, so `R = 0`), fix `τ₀ > 0` and let
the metric evolve by Perelman's `F`-flow `∂ₜ g = -2 (Ric + ∇²f)` with
`f = ‖x‖²/(4τ₀)` (fixed in time; the proved Hessian identity
`∇²f = g₀/(2τ₀)` from `GaussianShrinker` gives `∂ₜ g = -g₀/τ₀`).  The solution is
the scaling `g(t) = λ(t) g₀`, `λ(t) = 1 - t/τ₀` (`fflowMetricScale`); the metric is
positive definite exactly on the geometric domain `t < τ₀`.

The entropy measure is **fixed in time**: `ρ = gaussianKernel n τ₀` (the normalized
heat kernel, `∫ρ = 1`), i.e. `∂ₜ ρ ≡ 0` — the time-dependent-measure term of the
weighted-integral rule vanishes (`fflow_rho_deriv_zero`).

Under `g(t) = λ(t) g₀`:
* `|∇f|²_{g(t)} = λ⁻¹ ‖x‖²/(4τ₀²)` (`fflowGradSq`);
* `|Ric + ∇²f|²_{g(t)} = λ⁻² n/(4τ₀²)` (`fflowRiccHess`), because the Hessian is
  `∇²f = g₀/(2τ₀)` (Levi-Civita connection is scale-invariant) and the norm of a
  `(0,2)`-tensor rescales by `λ⁻²`; the constant `n/(4τ₀²)` is justified by
  `shrinker_riccHess_justified` (`fflow_riccHess_justified`).

## What is proved here

1. the pointwise time derivative `∂ₜ|∇f|²_{g(t)} = (1/τ₀)λ⁻²‖x‖²` **is not**
   `2|Ric+∇²f|² = 2λ⁻²n/(4τ₀²)` pointwise (`fflow_variation_ne_two_riccHess_at_zero`:
   the pointwise first-variation hypothesis of the D7-style reduction fails at
   `x = 0`; equality holds **iff** `‖x‖² = 2nτ₀`,
   `fflow_variation_eq_two_riccHess_iff` — the exact locus of the strong
   pointwise identity).  This is the honest
   divergence-term accounting: Perelman's identity lives at the integrated level;
2. the integrated cancellation *does* hold: `∫ ∂ₜ|∇f|²_{g(t)} dm = 2∫|Ric+∇²f|² dm`
   (`fflow_integrated_variation_eq_dissipation`), through the Gaussian moment
   `∫‖x‖²ρ = 2nτ₀` — this is the model's version of the integration by parts;
3. **the main theorem** `fflow_F_hasDerivAt`: differentiating the *genuine integral
   functional* `t ↦ F = ∫(|∇f|²) dm` by the delivered analytic theorem
   (`hasDerivAt_F_of_pointwise`) with all explicit regularity/domination/measurability
   obligations gives exactly
   `HasDerivAt (fun t => F(E t)) (FDissipationCorrected (E t)) t`
   on the geometric domain `t < τ₀`; the derivative is `n/(2(τ₀-t)²) > 0`
   (`fflow_F_deriv_pos`), so **Perelman's `F` is strictly increasing**
   (`fflow_F_strictMonoOn`, `fflow_F_increasing_on_Iio`);
4. the metric flow is the F-flow: `∂ₜλ = -2·(0 + 1/(2τ₀))` (`fflowMetricFlow_consistency`);
5. the literal D7 `FDerivativeStatement` (which pairs the derivative with the D3
   double-squared `FDissipation`) is **inconsistent** on this nontrivial model
   (`fflow_literal_FDerivative_inconsistent`: for `n = 1`, `τ₀ = 2`, at `t = 1` the
   computed derivative is `1/2` while `FDissipation = 1/8`), and it holds exactly
   under idempotency of the dissipation density (`fflow_literal_FDerivativeStatement_of_idempotent`),
   which on this model holds **iff** `n = 0`
   (`fflow_idempotency_iff_zero_dim`, `fflow_idempotency_forces_zero_dim`);
   the `n = 0` case is explicitly inhabited
   (`fflow_literal_FDerivativeStatement_zero_dim`: `F ≡ 0`, `FDissipation ≡ 0`,
   the literal D7 statement holds for every `t > 0`) — so the satisfiability of
   the idempotency hypothesis is a proved non-vacuity, and the degenerate case is
   the *only* one where the literal D7 field can hold on this model.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file.
-/
import Poincare.D12.EntropyVariation.GaussianShrinker

open MeasureTheory Real Filter TopologicalSpace Metric Set
open scoped Topology Filter InnerProductSpace RealInnerProductSpace
open Poincare.Longrun.Entropy
open Poincare.D10.HeatKernelEuclidean

namespace Poincare.D12.EntropyVariation

noncomputable section

/-! ## The metric scaling `λ(t) = 1 - t/τ₀` and its inverse -/

/-- The metric scale of the `F`-flow solution: `g(t) = λ(t) g₀` with `λ(t) = 1 - t/τ₀`.
Positive exactly for `t < τ₀` (the geometric domain). -/
noncomputable def fflowMetricScale (τ₀ t : ℝ) : ℝ := 1 - t / τ₀

/-- The inverse scale `λ(t)⁻¹ = τ₀/(τ₀ - t)`. -/
noncomputable def fflowScaleInv (τ₀ t : ℝ) : ℝ := τ₀ / (τ₀ - t)

/-- `∂ₜ λ(t) = -1/τ₀`. -/
theorem hasDerivAt_fflowMetricScale (τ₀ t : ℝ) :
    HasDerivAt (fun u => fflowMetricScale τ₀ u) (-1 / τ₀) t := by
  unfold fflowMetricScale
  have h : HasDerivAt (fun u : ℝ => 1 - u / τ₀) (0 - 1 / τ₀) t :=
    (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const τ₀)
  simpa [div_eq_mul_inv, one_div] using h

/-- **The model satisfies Perelman's `F`-flow**: `∂ₜ g = -2(Ric + ∇²f)` with `Ric = 0`
(flat model) and `∇²f = g₀/(2τ₀)` (the proved Hessian identity
`shrinker_hessian_eq_metricOverTwoTau`), i.e. `∂ₜ λ = -2·(0 + 1/(2τ₀)) = -1/τ₀`. -/
theorem fflowMetricFlow_consistency (τ₀ : ℝ) (hτ₀ : τ₀ ≠ 0) (t : ℝ) :
    HasDerivAt (fun u => fflowMetricScale τ₀ u) (-2 * (1 / (2 * τ₀))) t := by
  have h := hasDerivAt_fflowMetricScale τ₀ t
  have hval : -2 * (1 / (2 * τ₀)) = -1 / τ₀ := by
    field_simp [hτ₀]
  rwa [hval]

/-- `λ(t)⁻¹ = τ₀/(τ₀-t)` agrees with the inverse of `λ(t) = 1 - t/τ₀`. -/
theorem fflowScaleInv_eq_inv_metricScale (τ₀ t : ℝ) (hτ₀ : τ₀ ≠ 0) (ht : τ₀ - t ≠ 0) :
    fflowScaleInv τ₀ t = (fflowMetricScale τ₀ t)⁻¹ := by
  unfold fflowScaleInv fflowMetricScale
  field_simp [hτ₀, ht]

/-- Positivity of the inverse scale on the geometric domain. -/
theorem fflowScaleInv_pos {τ₀ t : ℝ} (hτ₀ : 0 < τ₀) (ht : t < τ₀) :
    0 < fflowScaleInv τ₀ t := by
  unfold fflowScaleInv
  positivity

/-- `∂ₜ λ⁻¹(t) = τ₀/(τ₀ - t)²`. -/
theorem hasDerivAt_fflowScaleInv (τ₀ t : ℝ) (ht : τ₀ - t ≠ 0) :
    HasDerivAt (fun u => fflowScaleInv τ₀ u) (τ₀ / (τ₀ - t) ^ 2) t := by
  unfold fflowScaleInv
  have hsub : HasDerivAt (fun u : ℝ => τ₀ - u) (-1 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_sub τ₀
  have hinv : HasDerivAt (fun u : ℝ => (τ₀ - u)⁻¹) (1 / (τ₀ - t) ^ 2) t := by
    have hraw : HasDerivAt (fun u : ℝ => (τ₀ - u)⁻¹) ((-(-1 : ℝ)) / (τ₀ - t) ^ 2) t :=
      hsub.inv ht
    simpa using hraw
  have hmain : HasDerivAt (fun u : ℝ => τ₀ * (τ₀ - u)⁻¹) (τ₀ * (1 / (τ₀ - t) ^ 2)) t :=
    hinv.const_mul τ₀
  have hval : τ₀ * (1 / (τ₀ - t) ^ 2) = τ₀ / (τ₀ - t) ^ 2 := by
    rw [one_div]
    rfl
  rw [hval] at hmain
  exact hmain

/-! ## The flow model data -/

/-- `|∇f|²` under the scaled metric: `λ⁻¹ ‖x‖²/(4τ₀²)`. -/
noncomputable def fflowGradSq (τ₀ t : ℝ) (x : Euc n) : ℝ :=
  fflowScaleInv τ₀ t * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))

/-- The honest pointwise time derivative of `t ↦ fflowGradSq τ₀ t x`:
`∂ₜ|∇f|²_{g(t)} = (1/τ₀)λ⁻²‖x‖² = (τ₀/((τ₀-t)²·4τ₀²))·‖x‖²`. -/
noncomputable def fflowGradSqVariation (τ₀ t : ℝ) (x : Euc n) : ℝ :=
  (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) * (‖x‖ ^ 2)

/-- `|Ric + ∇²f|²` under the scaled metric: `λ⁻² · n/(4τ₀²)` (Ric = 0 on the flat
model; `∇²f = g₀/(2τ₀)` and the `(0,2)`-tensor norm rescales by `λ⁻²`). -/
noncomputable def fflowRiccHess (n : ℕ) (τ₀ t : ℝ) : ℝ :=
  fflowScaleInv τ₀ t ^ 2 * shrinkerRiccHess n τ₀

/-- **The F-flow entropy datum at time `t`.**  Flat scalar curvature `R = 0`,
`|∇f|² = λ⁻¹‖x‖²/(4τ₀²)`, potential `f = ‖x‖²/(4τ₀)`, **time-independent** entropy
density `ρ = gaussianKernel n τ₀` (fixed measure), dissipation density
`λ⁻² n/(4τ₀²)`.  All integrability fields are discharged by the Gaussian moment
lemmas.  The datum is defined for every `t`; the geometric claims require `t < τ₀`. -/
noncomputable def fflowEntropyData (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (t : ℝ) :
    EntropyData (Euc n) volume where
  R := 0
  gradSq := fflowGradSq τ₀ t
  f := shrinkerFpot τ₀
  ρ := gaussianKernel n τ₀
  τ := τ₀
  τ_pos := hτ₀
  n := (n : ℝ)
  riccHess := fun _ => fflowRiccHess n τ₀ t
  ρ_nonneg := fun x => gaussianKernel_nonneg n (le_of_lt hτ₀) x
  integrable_F := by
    have hI := integrable_normSq_mul_gaussianKernel n hτ₀
    refine (hI.const_mul (fflowScaleInv τ₀ t / (4 * τ₀ ^ 2))).congr
      (eventually_of_forall fun x => ?_)
    change fflowScaleInv τ₀ t / (4 * τ₀ ^ 2) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x)
      = (0 + fflowGradSq τ₀ t x) * gaussianKernel n τ₀ x
    rw [fflowGradSq]
    ring
  integrable_W := by
    have hK : Integrable (fun x : Euc n => gaussianKernel n τ₀ x) := integrable_gaussianKernel n hτ₀
    have hNS : Integrable (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ₀ x) :=
      integrable_normSq_mul_gaussianKernel n hτ₀
    have hA : Integrable (fun x : Euc n => τ₀ * (fflowGradSq τ₀ t x * gaussianKernel n τ₀ x)) := by
      refine (hNS.const_mul (τ₀ * fflowScaleInv τ₀ t / (4 * τ₀ ^ 2))).congr
        (eventually_of_forall fun x => ?_)
      change τ₀ * fflowScaleInv τ₀ t / (4 * τ₀ ^ 2) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x)
        = τ₀ * (fflowGradSq τ₀ t x * gaussianKernel n τ₀ x)
      rw [fflowGradSq]
      ring
    have hB : Integrable (fun x : Euc n => (shrinkerFpot τ₀ x - (n : ℝ)) * gaussianKernel n τ₀ x) := by
      exact ((hNS.const_mul (1 / (4 * τ₀))).sub (hK.const_mul (n : ℝ))).congr
        (eventually_of_forall fun x => by
          change (1 / (4 * τ₀)) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x) - (n : ℝ) * gaussianKernel n τ₀ x
            = (shrinkerFpot τ₀ x - (n : ℝ)) * gaussianKernel n τ₀ x
          rw [shrinkerFpot]
          ring)
    exact (hA.add hB).congr (eventually_of_forall fun x => by
      change τ₀ * (fflowGradSq τ₀ t x * gaussianKernel n τ₀ x)
          + (shrinkerFpot τ₀ x - (n : ℝ)) * gaussianKernel n τ₀ x
        = (τ₀ * (fflowGradSq τ₀ t x + 0) + (shrinkerFpot τ₀ x - (n : ℝ))) * gaussianKernel n τ₀ x
      rw [fflowGradSq, shrinkerFpot]
      ring)

/-! ## Fixed measure: the time-dependent-measure obligation vanishes -/

/-- The entropy measure is fixed in time: `ρ` is independent of `t`. -/
theorem fflow_rho_timeIndep (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (s t : ℝ) :
    (fflowEntropyData n τ₀ hτ₀ s).ρ = (fflowEntropyData n τ₀ hτ₀ t).ρ := rfl

/-- **The time-dependent-measure term vanishes pointwise**: `∂ₜ ρ ≡ 0`
(Perelman's measure-preservation constraint, satisfied by the model). -/
theorem fflow_rho_deriv_zero (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (t : ℝ) (x : Euc n) :
    HasDerivAt (fun u => (fflowEntropyData n τ₀ hτ₀ u).ρ x) (0 : ℝ) t := by
  have h : (fun u => (fflowEntropyData n τ₀ hτ₀ u).ρ x) = fun _ : ℝ => gaussianKernel n τ₀ x := by
    funext u
    rfl
  rw [h]
  exact hasDerivAt_const t (gaussianKernel n τ₀ x)

/-! ## Pointwise derivative of the integrand and its mismatch with `2·riccHess` -/

/-- The pointwise time derivative of `t ↦ |∇f|²_{g(t)}(x)` is the honest variation
`(1/τ₀)λ⁻²‖x‖²`. -/
theorem hasDerivAt_fflowGradSq (τ₀ t : ℝ) (hτ₀ : τ₀ ≠ 0) (ht : τ₀ - t ≠ 0) (x : Euc n) :
    HasDerivAt (fun u => fflowGradSq τ₀ u x) (fflowGradSqVariation τ₀ t x) t := by
  unfold fflowGradSq fflowGradSqVariation
  have hder := hasDerivAt_fflowScaleInv τ₀ t ht
  have hmc : HasDerivAt (fun u => fflowScaleInv τ₀ u * (‖x‖ ^ 2 / (4 * τ₀ ^ 2)))
      ((τ₀ / (τ₀ - t) ^ 2) * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))) t :=
    hder.mul_const (‖x‖ ^ 2 / (4 * τ₀ ^ 2))
  have hval : (τ₀ / (τ₀ - t) ^ 2) * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))
      = (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 := by
    field_simp [hτ₀, ht, pow_ne_zero 2 ht, pow_ne_zero 2 hτ₀]
  rwa [← hval]

/-- `riccHess(t) = λ⁻² · riccHess(t=0)`: the dissipation density is the inverse-scale
squared times the shrinker density (the `(0,2)`-tensor norm rescales by `λ⁻²`). -/
theorem fflow_riccHess_eq_scaleInvSq_mul_shrinkerRiccHess (n : ℕ) (τ₀ t : ℝ) :
    fflowRiccHess n τ₀ t = fflowScaleInv τ₀ t ^ 2 * shrinkerRiccHess n τ₀ := rfl

/-- **The dissipation density of the flow model is justified pointwise**: it equals
`λ⁻²` times the Hilbert–Schmidt norm-squared of `∇²f = g₀/(2τ₀)` (the proved Hessian
identity `shrinker_riccHess_justified`); `Ric = 0` on the flat model. -/
theorem fflow_riccHess_justified (n : ℕ) (τ₀ t : ℝ) (hτ₀ : τ₀ ≠ 0) :
    fflowRiccHess n τ₀ t = fflowScaleInv τ₀ t ^ 2 *
      (∑ i : Fin n, ∑ j : Fin n, (((1 / (2 * τ₀)) * ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        EuclideanSpace.basisFun (Fin n) ℝ j⟫_ℝ)) ^ 2) := by
  unfold fflowRiccHess
  rw [shrinker_riccHess_justified n τ₀ hτ₀ (0 : Euc n)]

/-- Positivity of `2·riccHess` on the nontrivial geometric model. -/
theorem fflow_two_riccHess_pos (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (hn : 0 < n) {t : ℝ}
    (ht : t < τ₀) :
    0 < 2 * fflowRiccHess n τ₀ t := by
  unfold fflowRiccHess shrinkerRiccHess
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h1 : 0 < fflowScaleInv τ₀ t ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt (fflowScaleInv_pos hτ₀ ht))
  have h2 : 0 < (n : ℝ) / (4 * τ₀ ^ 2) := div_pos hn' (by positivity)
  positivity

/-- **The pointwise first-variation identity fails at `x = 0`.**  The honest
pointwise derivative `∂ₜ|∇f|²_{g(t)}` is *not* `2·riccHess` pointwise: at `x = 0`
the derivative is `0` while `2·riccHess > 0`.  Consequently the strong pointwise
hypothesis `hfirstVariation` of the D7-style reduction (`fDerivativeCorrected_at_of_pointwise`)
is not satisfiable on this model — Perelman's identity holds only after integration,
where the divergence term is cancelled by the Gaussian moment identity. -/
theorem fflow_variation_ne_two_riccHess_at_zero (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (hn : 0 < n)
    {t : ℝ} (ht : t < τ₀) :
    fflowGradSqVariation τ₀ t (0 : Euc n) ≠ 2 * fflowRiccHess n τ₀ t := by
  intro h
  have hzero : fflowGradSqVariation τ₀ t (0 : Euc n) = 0 := by simp [fflowGradSqVariation]
  rw [hzero] at h
  have hpos : 0 < 2 * fflowRiccHess n τ₀ t := fflow_two_riccHess_pos n τ₀ hτ₀ hn ht
  linarith

/-- The pointwise identity `∂ₜ|∇f|² = 2·riccHess` holds exactly on the sphere
`‖x‖² = 2nτ₀` (where the divergence term vanishes). -/
theorem fflow_variation_eq_two_riccHess_of_normSq_eq (n : ℕ) (τ₀ : ℝ) (hτ₀ : τ₀ ≠ 0)
    {t : ℝ} (ht : τ₀ - t ≠ 0) (x : Euc n) (hx : ‖x‖ ^ 2 = 2 * (n : ℝ) * τ₀) :
    fflowGradSqVariation τ₀ t x = 2 * fflowRiccHess n τ₀ t := by
  unfold fflowGradSqVariation fflowRiccHess shrinkerRiccHess fflowScaleInv
  rw [hx]
  field_simp [hτ₀, ht, pow_ne_zero 2 ht, pow_ne_zero 2 hτ₀]

/-- **The exact locus of the pointwise first-variation identity (iff).**
`∂ₜ|∇f|²_{g(t)}(x) = 2|Ric + ∇²f|²_{g(t)}(x)` holds **if and only if**
`‖x‖² = 2nτ₀`.  Combined with `fflow_variation_ne_two_riccHess_at_zero` this pins
down exactly where the strong pointwise hypothesis of the D7-style reduction is
satisfied on the model: on the radius-`√(2nτ₀)` sphere only, nowhere else
(in particular not at `x = 0`). -/
theorem fflow_variation_eq_two_riccHess_iff (n : ℕ) (τ₀ : ℝ) (hτ₀ : τ₀ ≠ 0)
    {t : ℝ} (ht : τ₀ - t ≠ 0) (x : Euc n) :
    fflowGradSqVariation τ₀ t x = 2 * fflowRiccHess n τ₀ t ↔ ‖x‖ ^ 2 = 2 * (n : ℝ) * τ₀ := by
  constructor
  · intro h
    have h' : τ₀ * ‖x‖ ^ 2 = 2 * (n : ℝ) * τ₀ ^ 2 := by
      unfold fflowGradSqVariation fflowRiccHess shrinkerRiccHess fflowScaleInv at h
      have hden : (τ₀ - t) ^ 2 * (4 * τ₀ ^ 2) ≠ 0 := by
        exact mul_ne_zero (pow_ne_zero 2 ht) (by
          have hsq : τ₀ ^ 2 ≠ 0 := pow_ne_zero 2 hτ₀
          positivity)
      field_simp [hden, pow_ne_zero 2 ht, pow_ne_zero 2 hτ₀] at h ⊢
      nlinarith
    exact mul_left_cancel₀ hτ₀ (by
      calc
        τ₀ * ‖x‖ ^ 2 = 2 * (n : ℝ) * τ₀ ^ 2 := h'
        _ = τ₀ * (2 * (n : ℝ) * τ₀) := by ring)
  · intro hx
    exact fflow_variation_eq_two_riccHess_of_normSq_eq n τ₀ hτ₀ ht x hx

/-! ## Integrated values: the divergence term is cancelled by the moment identity -/

/-- The integrated honest variation, computed by the Gaussian moment: `n/(2(τ₀-t)²)`. -/
theorem fflow_variation_integral (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) {t : ℝ} (ht : τ₀ - t ≠ 0) :
    ∫ x : Euc n, fflowGradSqVariation τ₀ t x * gaussianKernel n τ₀ x
      = (n : ℝ) / (2 * (τ₀ - t) ^ 2) := by
  unfold fflowGradSqVariation
  have hfun : (fun x : Euc n => (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 * gaussianKernel n τ₀ x)
      = fun x : Euc n => (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x) := by
    funext x
    ring
  rw [hfun,
    integral_const_mul (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ₀ x),
    integral_normSq_mul_gaussianKernel n hτ₀]
  field_simp [ht, ne_of_gt hτ₀, pow_ne_zero 2 ht, pow_ne_zero 2 (ne_of_gt hτ₀)]
  ring

/-- The corrected dissipation of the flow model: `n/(2(τ₀-t)²)`. -/
theorem fflow_FDissipationCorrected_value (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) {t : ℝ}
    (ht : τ₀ - t ≠ 0) :
    FDissipationCorrected (fflowEntropyData n τ₀ hτ₀ t) = (n : ℝ) / (2 * (τ₀ - t) ^ 2) := by
  unfold FDissipationCorrected
  simp only [fflowEntropyData, fflowRiccHess, shrinkerRiccHess]
  rw [integral_const_mul (2 * (fflowScaleInv τ₀ t ^ 2 * ((n : ℝ) / (4 * τ₀ ^ 2))))
      (fun x : Euc n => gaussianKernel n τ₀ x),
    gaussianKernel_integral n hτ₀]
  unfold fflowScaleInv
  field_simp [ht, ne_of_gt hτ₀, pow_ne_zero 2 ht, pow_ne_zero 2 (ne_of_gt hτ₀)]
  ring

/-- **The integrated first variation equals the corrected dissipation.**
`∫ ∂ₜ|∇f|²_{g(t)} dm = ∫ 2·riccHess·ρ dm = n/(2(τ₀-t)²)`: the pointwise mismatch of
`fflow_variation_ne_two_riccHess_at_zero` disappears after integration because
`∫‖x‖²ρ = 2nτ₀` — the model's exact replacement for the integration-by-parts step. -/
theorem fflow_integrated_variation_eq_dissipation (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) {t : ℝ}
    (ht : τ₀ - t ≠ 0) :
    ∫ x : Euc n, fflowGradSqVariation τ₀ t x * gaussianKernel n τ₀ x
      = FDissipationCorrected (fflowEntropyData n τ₀ hτ₀ t) := by
  rw [fflow_variation_integral n τ₀ hτ₀ ht, fflow_FDissipationCorrected_value n τ₀ hτ₀ ht]

/-- The D3 double-squared `FDissipation` of the flow model: `n²/(8(τ₀-t)⁴)`.  This
differs from the corrected value `n/(2(τ₀-t)²)` whenever
`4(τ₀-t)² ≠ n τ₀⁰·…`, i.e. generically. -/
theorem fflow_FDissipation_value (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) {t : ℝ} (ht : τ₀ - t ≠ 0) :
    EntropyData.FDissipation (fflowEntropyData n τ₀ hτ₀ t) = (n : ℝ) ^ 2 / (8 * (τ₀ - t) ^ 4) := by
  simp only [EntropyData.FDissipation, fflowEntropyData, fflowRiccHess, shrinkerRiccHess]
  unfold fflowScaleInv
  rw [integral_const_mul (2 * ((τ₀ / (τ₀ - t)) ^ 2 * ((n : ℝ) / (4 * τ₀ ^ 2))) ^ 2)
      (fun x : Euc n => gaussianKernel n τ₀ x),
    gaussianKernel_integral n hτ₀]
  field_simp [ht, ne_of_gt hτ₀, pow_ne_zero 2 ht, pow_ne_zero 2 (ne_of_gt hτ₀)]
  ring

/-- The `F`-functional of the flow model: `F(t) = n/(2(τ₀-t))` (equivalently
`λ⁻¹·n/(2τ₀)`, extending the shrinker value `n/(2τ₀)` at `t = 0`). -/
theorem fflow_F_value (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) {t : ℝ} (ht : τ₀ - t ≠ 0) :
    EntropyData.F (fflowEntropyData n τ₀ hτ₀ t) = (n : ℝ) / (2 * (τ₀ - t)) := by
  simp only [EntropyData.F, fflowEntropyData, fflowGradSq]
  change ∫ x : Euc n, (0 + fflowScaleInv τ₀ t * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))) * gaussianKernel n τ₀ x
    = (n : ℝ) / (2 * (τ₀ - t))
  have hfun : (fun x : Euc n => (0 + fflowScaleInv τ₀ t * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))) * gaussianKernel n τ₀ x)
      = fun x : Euc n => fflowScaleInv τ₀ t * ((‖x‖ ^ 2 / (4 * τ₀ ^ 2)) * gaussianKernel n τ₀ x) := by
    funext x
    ring
  rw [hfun,
    integral_const_mul (fflowScaleInv τ₀ t) (fun x : Euc n => (‖x‖ ^ 2 / (4 * τ₀ ^ 2)) * gaussianKernel n τ₀ x)]
  have hfun2 : (fun x : Euc n => (‖x‖ ^ 2 / (4 * τ₀ ^ 2)) * gaussianKernel n τ₀ x)
      = fun x : Euc n => (1 / (4 * τ₀ ^ 2)) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x) := by
    funext x
    ring
  rw [hfun2,
    integral_const_mul (1 / (4 * τ₀ ^ 2)) (fun x : Euc n => ‖x‖ ^ 2 * gaussianKernel n τ₀ x),
    integral_normSq_mul_gaussianKernel n hτ₀]
  unfold fflowScaleInv
  field_simp [ht, ne_of_gt hτ₀, pow_ne_zero 2 (ne_of_gt hτ₀)]
  ring

/-! ## The main theorem: `dF/dt = 2∫|Ric+∇²f|² dm`, proved, not assumed -/

/-- **First variation of `F` along the F-flow (the main theorem).**

On the geometric domain `t < τ₀`, differentiating the genuine integral functional
`t ↦ F (E t) = ∫ (0 + λ⁻¹‖x‖²/(4τ₀²)) ρ dx` through the delivered analytic theorem
`Poincare.D12.EntropyVariation.hasDerivAt_F_of_pointwise` — with the fixed-measure
statement `∂ₜρ ≡ 0`, the honest pointwise variation, and explicit
measurability/integrability/domination obligations — gives

`HasDerivAt (fun t => F (E t)) (FDissipationCorrected (E t)) t`,

i.e. Perelman's `dF/dt = 2∫|Ric+∇²f|² dm` on the model.  Nothing is assumed about
`FDerivativeStatement` or monotonicity: the derivative is proved. -/
theorem fflow_F_hasDerivAt (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) {t : ℝ} (ht : t < τ₀) :
    HasDerivAt (fun u => (fflowEntropyData n τ₀ hτ₀ u).F)
      (FDissipationCorrected (fflowEntropyData n τ₀ hτ₀ t)) t := by
  let E : ℝ → EntropyData (Euc n) volume := fun u => fflowEntropyData n τ₀ hτ₀ u
  let variation : ℝ → Euc n → ℝ := fun u x => fflowGradSqVariation τ₀ u x
  let bound : Euc n → ℝ := fun x => (1 / ((τ₀ - t) ^ 2 * τ₀)) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x)
  let s : Set ℝ := ball t ((τ₀ - t) / 2)
  have hposd : 0 < (τ₀ - t) / 2 := by positivity
  have hs : s ∈ 𝓝 t := ball_mem_nhds t hposd
  have hu_pos : ∀ u ∈ s, 0 < τ₀ - u := by
    intro u hu
    have hmem := mem_ball.mp hu
    have habs : |u - t| < (τ₀ - t) / 2 := by simpa [dist_eq_norm] using hmem
    have huub : u < t + (τ₀ - t) / 2 := by linarith [(abs_lt.mp habs).2]
    have h' : (τ₀ - t) / 2 < τ₀ - t := by
      rw [← sub_pos]
      have hd : (τ₀ - t) - (τ₀ - t) / 2 = (τ₀ - t) / 2 := by ring_nf
      rw [hd]
      exact hposd
    have htgt : t + (τ₀ - t) / 2 < τ₀ := by linarith
    exact sub_pos.mpr (lt_trans huub htgt)
  have hu_ne : ∀ u ∈ s, τ₀ - u ≠ 0 := fun u hu => ne_of_gt (hu_pos u hu)
  have hmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (fun x => ((E u).R x + (E u).gradSq x) * (E u).ρ x) := by
    filter_upwards with u
    unfold E
    simp only [fflowEntropyData]
    change AEStronglyMeasurable (fun x : Euc n => (0 + fflowGradSq τ₀ u x) * gaussianKernel n τ₀ x)
    have hg : AEStronglyMeasurable (fun x : Euc n => 0 + fflowGradSq τ₀ u x) := by
      unfold fflowGradSq
      fun_prop
    exact hg.mul (continuous_gaussianKernel n).aestronglyMeasurable
  have hint : Integrable (fun x => ((E t).R x + (E t).gradSq x) * (E t).ρ x) := by
    unfold E
    exact (fflowEntropyData n τ₀ hτ₀ t).integrable_F
  have hmeas' : AEStronglyMeasurable (fun x => variation t x * (E t).ρ x + ((E t).R x + (E t).gradSq x) * (0 : ℝ)) := by
    unfold E variation
    simp only [fflowEntropyData, fflowGradSq, fflowGradSqVariation]
    change AEStronglyMeasurable (fun x : Euc n =>
      (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 * gaussianKernel n τ₀ x
        + (0 + fflowScaleInv τ₀ t * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))) * (0 : ℝ))
    have hg : AEStronglyMeasurable (fun x : Euc n =>
      (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 * gaussianKernel n τ₀ x
        + (0 + fflowScaleInv τ₀ t * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))) * (0 : ℝ)) := by
      have h1 : AEStronglyMeasurable (fun x : Euc n => (τ₀ / ((τ₀ - t) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2) := by
        fun_prop
      have h2 : AEStronglyMeasurable (fun x : Euc n => 0 + fflowScaleInv τ₀ t * (‖x‖ ^ 2 / (4 * τ₀ ^ 2))) := by
        fun_prop
      exact (h1.mul (continuous_gaussianKernel n).aestronglyMeasurable).add (h2.mul_const (0 : ℝ))
    exact hg
  have hpoint : ∀ᵐ x ∂volume, ∀ u ∈ s, HasDerivAt (fun v => (E v).R x + (E v).gradSq x) (variation u x) u := by
    filter_upwards with x u hu
    unfold E
    have hg : HasDerivAt (fun v => fflowGradSq τ₀ v x) (fflowGradSqVariation τ₀ u x) u :=
      hasDerivAt_fflowGradSq τ₀ u (ne_of_gt hτ₀) (hu_ne u hu) x
    change HasDerivAt (fun v => (fflowEntropyData n τ₀ hτ₀ v).R x + (fflowEntropyData n τ₀ hτ₀ v).gradSq x)
      (variation u x) u
    change HasDerivAt (fun v => 0 + fflowGradSq τ₀ v x) (variation u x) u
    exact hg.const_add (0 : ℝ)
  have hrho : ∀ᵐ x ∂volume, ∀ u ∈ s, HasDerivAt (fun v => (E v).ρ x) (0 : ℝ) u := by
    filter_upwards with x u hu
    have h : (fun v => (E v).ρ x) = fun _ : ℝ => gaussianKernel n τ₀ x := by
      funext v
      unfold E
      rfl
    rw [h]
    exact hasDerivAt_const u (gaussianKernel n τ₀ x)
  have hdom : ∀ᵐ x ∂volume, ∀ u ∈ s,
      ‖variation u x * (E u).ρ x + ((E u).R x + (E u).gradSq x) * (0 : ℝ)‖ ≤ bound x := by
    filter_upwards with x u hu
    have hnonneg : 0 ≤ variation u x * (E u).ρ x + ((E u).R x + (E u).gradSq x) * (0 : ℝ) := by
      unfold E variation fflowGradSqVariation
      simp only [fflowEntropyData]
      have hc : 0 ≤ (τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2))) * (‖x‖ ^ 2) := by
        have h1 : 0 ≤ τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2)) := by
          have hsq : 0 < (τ₀ - u) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (hu_pos u hu))
          have hden : 0 < (τ₀ - u) ^ 2 * (4 * τ₀ ^ 2) := mul_pos hsq (by positivity)
          exact le_of_lt (div_pos hτ₀ hden)
        exact mul_nonneg h1 (sq_nonneg ‖x‖)
      have hmain : 0 ≤ (τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 * gaussianKernel n τ₀ x :=
        mul_nonneg hc (gaussianKernel_nonneg n (le_of_lt hτ₀) x)
      change 0 ≤ (τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 * gaussianKernel n τ₀ x
        + (0 + fflowGradSq τ₀ u x) * (0 : ℝ)
      have hzero : (0 + fflowGradSq τ₀ u x) * (0 : ℝ) = 0 := by ring
      rw [hzero, add_zero]
      exact hmain
    rw [norm_of_nonneg hnonneg]
    unfold E variation fflowGradSqVariation bound
    simp only [fflowEntropyData]
    change (τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 * gaussianKernel n τ₀ x
        + (0 + fflowGradSq τ₀ u x) * (0 : ℝ)
        ≤ (1 / ((τ₀ - t) ^ 2 * τ₀)) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x)
    have hshape : (τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2))) * ‖x‖ ^ 2 * gaussianKernel n τ₀ x
        + (0 + fflowGradSq τ₀ u x) * (0 : ℝ)
        = (τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2))) * (‖x‖ ^ 2 * gaussianKernel n τ₀ x) := by
      ring
    rw [hshape]
    have hcoef : τ₀ / ((τ₀ - u) ^ 2 * (4 * τ₀ ^ 2)) ≤ 1 / ((τ₀ - t) ^ 2 * τ₀) := by
      have hge : (τ₀ - t) / 2 < τ₀ - u := by
        have hmem := mem_ball.mp hu
        have habs : |u - t| < (τ₀ - t) / 2 := by simpa [dist_eq_norm] using hmem
        have huub : u < t + (τ₀ - t) / 2 := by linarith [(abs_lt.mp habs).2]
        linarith
      have hle1 : (τ₀ - t) ≤ 2 * (τ₀ - u) := by nlinarith [sub_pos.mpr ht]
      have hsq : (τ₀ - t) ^ 2 ≤ (2 * (τ₀ - u)) ^ 2 :=
        pow_le_pow_left₀ (by positivity : 0 ≤ τ₀ - t) hle1 2
      have hsq' : (τ₀ - t) ^ 2 ≤ 4 * (τ₀ - u) ^ 2 := by
        nlinarith
      have hmul : τ₀ ^ 2 * (τ₀ - t) ^ 2 ≤ τ₀ ^ 2 * (4 * (τ₀ - u) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq' (sq_nonneg τ₀)
      have hsqposu : 0 < (τ₀ - u) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (hu_pos u hu))
      have hsqpost : 0 < (τ₀ - t) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr ht))
      rw [div_le_div_iff₀ (mul_pos hsqposu (by positivity : 0 < 4 * τ₀ ^ 2))
        (mul_pos hsqpost hτ₀)]
      nlinarith
    exact mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (sq_nonneg ‖x‖) (gaussianKernel_nonneg n (le_of_lt hτ₀) x))
  have hbound : Integrable bound := by
    unfold bound
    refine ((integrable_normSq_mul_gaussianKernel n hτ₀).const_mul (1 / ((τ₀ - t) ^ 2 * τ₀))).congr
      (eventually_of_forall fun _ => rfl)
  have hmain := hasDerivAt_F_of_pointwise E variation (fun _ _ => (0 : ℝ)) (bound := bound)
    hs hmeas hint hmeas' hpoint hrho hdom hbound
  have hder : (∫ x, variation t x * (E t).ρ x + ((E t).R x + (E t).gradSq x) * (0 : ℝ) ∂volume)
      = FDissipationCorrected (E t) := by
    unfold E variation
    simp only [fflowEntropyData]
    change (∫ x : Euc n, fflowGradSqVariation τ₀ t x * gaussianKernel n τ₀ x
        + (0 + fflowGradSq τ₀ t x) * (0 : ℝ))
      = FDissipationCorrected (fflowEntropyData n τ₀ hτ₀ t)
    have h1 : (∫ x : Euc n, fflowGradSqVariation τ₀ t x * gaussianKernel n τ₀ x
        + (0 + fflowGradSq τ₀ t x) * (0 : ℝ))
        = ∫ x : Euc n, fflowGradSqVariation τ₀ t x * gaussianKernel n τ₀ x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h1, fflow_variation_integral n τ₀ hτ₀ (ne_of_gt (sub_pos.mpr ht)),
      fflow_FDissipationCorrected_value n τ₀ hτ₀ (ne_of_gt (sub_pos.mpr ht))]
  dsimp only [E] at hmain hder
  rwa [hder] at hmain

/-- The first variation in closed form: `dF/dt = n/(2(τ₀-t)²)`. -/
theorem fflow_F_hasDerivAt_closedForm (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) {t : ℝ} (ht : t < τ₀) :
    HasDerivAt (fun u => (fflowEntropyData n τ₀ hτ₀ u).F) ((n : ℝ) / (2 * (τ₀ - t) ^ 2)) t := by
  have hmain := fflow_F_hasDerivAt n τ₀ hτ₀ ht
  rwa [fflow_FDissipationCorrected_value n τ₀ hτ₀ (ne_of_gt (sub_pos.mpr ht))] at hmain

/-- The corrected first-variation statement on the geometric domain, uniformly in
time — the corrected analogue of the D7 `FDerivativeStatement`, here *derived*. -/
theorem fflow_corrected_FDerivative_on_domain (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    ∀ t : ℝ, 0 < t → t < τ₀ → HasDerivAt (fun u => (fflowEntropyData n τ₀ hτ₀ u).F)
      (FDissipationCorrected (fflowEntropyData n τ₀ hτ₀ t)) t := by
  intro t _ht0 ht
  exact fflow_F_hasDerivAt n τ₀ hτ₀ ht

/-- **The derivative is positive**: Perelman's `F` increases along the F-flow on the
geometric domain (for `n ≥ 1`). -/
theorem fflow_F_deriv_pos (n : ℕ) (τ₀ : ℝ) (_hτ₀ : 0 < τ₀) (hn : 0 < n) {t : ℝ} (ht : t < τ₀) :
    0 < (n : ℝ) / (2 * (τ₀ - t) ^ 2) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < (τ₀ - t) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr ht))
  positivity

/-- **Strict monotonicity of `F` along the F-flow** on the geometric domain: from the
closed form `F(t) = n/(2(τ₀-t))`, for `n ≥ 1` and `s < t < τ₀` one has
`F(E s) < F(E t)`. -/
theorem fflow_F_strictMonoOn (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (hn : 0 < n) :
    StrictMonoOn (fun u => (fflowEntropyData n τ₀ hτ₀ u).F) (Iio τ₀) := by
  intro s hs t ht hst
  have hsτ : s < τ₀ := hs
  have htτ : t < τ₀ := ht
  change (fflowEntropyData n τ₀ hτ₀ s).F < (fflowEntropyData n τ₀ hτ₀ t).F
  rw [fflow_F_value n τ₀ hτ₀ (ne_of_gt (sub_pos.mpr hsτ)),
    fflow_F_value n τ₀ hτ₀ (ne_of_gt (sub_pos.mpr htτ))]
  have h0 : 0 < τ₀ - t := sub_pos.mpr htτ
  have hts : τ₀ - t < τ₀ - s := by linarith
  have hinv : 1 / (τ₀ - s) < 1 / (τ₀ - t) := one_div_lt_one_div_of_lt h0 hts
  have hn' : 0 < (n : ℝ) / 2 := by positivity
  have hmul : (n : ℝ) / 2 * (1 / (τ₀ - s)) < (n : ℝ) / 2 * (1 / (τ₀ - t)) :=
    mul_lt_mul_of_pos_left hinv hn'
  have h1 : (n : ℝ) / 2 * (1 / (τ₀ - s)) = (n : ℝ) / (2 * (τ₀ - s)) := by
    field_simp [ne_of_gt (sub_pos.mpr hsτ)]
  have h2 : (n : ℝ) / 2 * (1 / (τ₀ - t)) = (n : ℝ) / (2 * (τ₀ - t)) := by
    field_simp [ne_of_gt h0]
  rwa [h1, h2] at hmul

/-- Interval form: for `s < t < τ₀` and `n ≥ 1`, `F(E s) < F(E t)`. -/
theorem fflow_F_increasing_on_Iio (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (hn : 0 < n) :
    ∀ s t : ℝ, s < t → t < τ₀ →
      (fflowEntropyData n τ₀ hτ₀ s).F < (fflowEntropyData n τ₀ hτ₀ t).F := by
  intro s t hst ht
  have hmono := fflow_F_strictMonoOn n τ₀ hτ₀ hn
  exact hmono (show s ∈ Iio τ₀ from lt_trans hst ht) ht hst

/-! ## The D3/D7 literal dissipation on this model: where it can and cannot hold -/

/-- Witness: on the nontrivial model (`n = 1`, `τ₀ = 2`, at `t = 1`) the D3
`FDissipation = 1/8` differs from the corrected value `1/2`. -/
theorem fflow_FDissipation_ne_corrected_one (h2 : 0 < (2 : ℝ)) :
    EntropyData.FDissipation (fflowEntropyData 1 2 h2 (1 : ℝ)) ≠
      FDissipationCorrected (fflowEntropyData 1 2 h2 (1 : ℝ)) := by
  rw [fflow_FDissipation_value 1 2 h2 (by norm_num : (2 : ℝ) - 1 ≠ 0),
    fflow_FDissipationCorrected_value 1 2 h2 (by norm_num : (2 : ℝ) - 1 ≠ 0)]
  norm_num

/-- **The literal D7 `FDerivativeStatement` is inconsistent on this model.**
For `n = 1`, `τ₀ = 2`, the computed derivative of `F` at `t = 1` is `1/2`
(`fflow_F_hasDerivAt_closedForm`), while `FDissipation = 1/8`; uniqueness of
`HasDerivAt` forces the contradiction.  This records *why* the literal D7 field
(carrying the D3 double-squared dissipation) cannot hold on a nontrivial model
with non-idempotent density `λ⁻²n/(4τ₀²) ∉ {0,1}`. -/
theorem fflow_literal_FDerivative_inconsistent :
    ¬ FDerivativeStatement (fun u => fflowEntropyData 1 2 (by norm_num : (0 : ℝ) < 2) u) := by
  intro h
  let E : ℝ → EntropyData (Euc 1) volume := fun u => fflowEntropyData 1 2 (by norm_num) u
  have hder : HasDerivAt (fun u => (E u).F) ((1 : ℝ) / 2) (1 : ℝ) := by
    unfold E
    convert fflow_F_hasDerivAt_closedForm 1 2 (by norm_num) (by norm_num : (1 : ℝ) < 2) using 1
    norm_num
  have hlit := h (1 : ℝ) (by norm_num : 0 < (1 : ℝ))
  have hFD : EntropyData.FDissipation (fflowEntropyData 1 2 (by norm_num) (1 : ℝ)) = (1 : ℝ) / 8 := by
    rw [fflow_FDissipation_value 1 2 (by norm_num) (by norm_num : (2 : ℝ) - 1 ≠ 0)]
    norm_num
  have hlit' : HasDerivAt (fun u => (E u).F) ((1 : ℝ) / 8) (1 : ℝ) := by
    unfold E
    simpa [hFD] using hlit
  have hEq := hder.unique hlit'
  norm_num at hEq

/-- **Where the literal D7 statement can hold**: under pointwise idempotency of the
dissipation density at every time of the geometric domain, the corrected first
variation yields the literal D7 `FDerivativeStatement`-style identity
(derivative `= FDissipation (E t)`, the D3 double-squared dissipation).  On the
flow model this forces `λ(t)⁻² n/(4τ₀²) ∈ {0,1}` for all `t` in the domain —
the degenerate (idempotent) cases only. -/
theorem fflow_literal_FDerivativeStatement_of_idempotent (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hidem : ∀ t : ℝ, 0 < t → t < τ₀ → fflowRiccHess n τ₀ t ^ 2 = fflowRiccHess n τ₀ t) :
    ∀ t : ℝ, 0 < t → t < τ₀ → HasDerivAt (fun u => (fflowEntropyData n τ₀ hτ₀ u).F)
      (EntropyData.FDissipation (fflowEntropyData n τ₀ hτ₀ t)) t := by
  intro t ht0 ht
  have hcorr := fflow_F_hasDerivAt n τ₀ hτ₀ ht
  have hidem' : ∀ x : Euc n, (fflowEntropyData n τ₀ hτ₀ t).riccHess x ^ 2
      = (fflowEntropyData n τ₀ hτ₀ t).riccHess x := by
    intro x
    simpa [fflowEntropyData] using hidem t ht0 ht
  have hFD := FDissipation_eq_corrected_of_idempotent (fflowEntropyData n τ₀ hτ₀ t) hidem'
  rw [← hFD] at hcorr
  exact hcorr

/-! ## Exact satisfiability of the idempotency hypothesis; the `n = 0` witness -/

/-- On the zero-dimensional model the dissipation density vanishes: `riccHess = 0`
for all `t` (the only vector of `Euc 0` has norm `0`). -/
theorem fflow_riccHess_eq_zero_of_zero_dim (τ₀ t : ℝ) :
    fflowRiccHess 0 τ₀ t = 0 := by
  unfold fflowRiccHess shrinkerRiccHess
  norm_num

/-- Idempotency `riccHess² = riccHess` holds on the zero-dimensional model
(trivially: the density is `0`). -/
theorem fflow_idempotency_holds_zero_dim (τ₀ t : ℝ) :
    fflowRiccHess 0 τ₀ t ^ 2 = fflowRiccHess 0 τ₀ t := by
  rw [fflow_riccHess_eq_zero_of_zero_dim τ₀ t]
  norm_num

/-- **The idempotency hypothesis forces the zero-dimensional case.**  If
`riccHess(t)² = riccHess(t)` holds for **all** `t` of the geometric domain
`(0, τ₀)`, then `n = 0`.  Proof: `riccHess(t) = λ(t)⁻² · n/(4τ₀²)` with
`λ(t) = 1 - t/τ₀`; idempotency at `t = τ₀/2` (where `λ⁻² = 4`) forces
`n/(4τ₀²) ∈ {0, 1/4}`, while idempotency at `t = 3τ₀/4` (where `λ⁻² = 16`)
forces `n/(4τ₀²) ∈ {0, 1/16}`; the only common value is `0`, i.e. `n = 0`.
Combined with `fflow_idempotency_holds_zero_dim`, the literal D7
`FDerivativeStatement`-style identity is satisfiable on the flow model
**exactly** in the degenerate case `n = 0` — and is inconsistent for every
nontrivial model (`fflow_literal_FDerivative_inconsistent` for `n = 1`). -/
theorem fflow_idempotency_forces_zero_dim (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hidem : ∀ t : ℝ, 0 < t → t < τ₀ → fflowRiccHess n τ₀ t ^ 2 = fflowRiccHess n τ₀ t) :
    n = 0 := by
  let c : ℝ := (n : ℝ) / (4 * τ₀ ^ 2)
  have hh2 : 0 < τ₀ / 2 := by positivity
  have hh2lt : τ₀ / 2 < τ₀ := by nlinarith
  have h3q : 0 < 3 * τ₀ / 4 := by positivity
  have h3qlt : 3 * τ₀ / 4 < τ₀ := by nlinarith
  have h1 := hidem (τ₀ / 2) hh2 hh2lt
  have h2 := hidem (3 * τ₀ / 4) h3q h3qlt
  have hinv12 : fflowScaleInv τ₀ (τ₀ / 2) = 2 := by
    unfold fflowScaleInv
    have hsub : τ₀ - τ₀ / 2 ≠ 0 := by nlinarith
    field_simp [ne_of_gt hτ₀, hsub]
    ring
  have hinv34 : fflowScaleInv τ₀ (3 * τ₀ / 4) = 4 := by
    unfold fflowScaleInv
    have hsub : τ₀ - 3 * τ₀ / 4 ≠ 0 := by nlinarith
    field_simp [ne_of_gt hτ₀, hsub]
    ring
  have h1c : (4 * c) ^ 2 = 4 * c := by
    unfold fflowRiccHess shrinkerRiccHess at h1
    rw [hinv12] at h1
    dsimp [c]
    norm_num at h1 ⊢
    exact h1
  have h2c : (16 * c) ^ 2 = 16 * c := by
    unfold fflowRiccHess shrinkerRiccHess at h2
    rw [hinv34] at h2
    dsimp [c]
    norm_num at h2 ⊢
    exact h2
  have hc0 : c = 0 := by
    by_contra hcne
    have hc1 : 4 * c = 1 := by
      have hz : (4 * c) * (4 * c - 1) = 0 := by nlinarith [h1c]
      have hz' := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hcne)
      nlinarith
    have hc2 : 16 * c = 1 := by
      have hz : (16 * c) * (16 * c - 1) = 0 := by nlinarith [h2c]
      have hz' := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hcne)
      nlinarith
    nlinarith
  have hn0 : (n : ℝ) = 0 := by
    dsimp [c] at hc0
    have hden : 4 * τ₀ ^ 2 ≠ 0 := by
      have hsq : τ₀ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hτ₀)
      positivity
    field_simp [hden] at hc0
    simpa using hc0
  exact Nat.cast_eq_zero.mp hn0

/-- **The idempotency hypothesis is satisfiable exactly in the zero-dimensional
case** (iff version). -/
theorem fflow_idempotency_iff_zero_dim (n : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    (∀ t : ℝ, 0 < t → t < τ₀ → fflowRiccHess n τ₀ t ^ 2 = fflowRiccHess n τ₀ t) ↔ n = 0 := by
  constructor
  · intro hidem
    exact fflow_idempotency_forces_zero_dim n τ₀ hτ₀ hidem
  · intro hn
    subst hn
    intro t _ht0 _htτ
    exact fflow_idempotency_holds_zero_dim τ₀ t

/-- **The literal D7 `FDerivativeStatement` holds on the zero-dimensional flow
model: a concrete (degenerate) satisfiability witness.**  For `n = 0` both
`F ≡ 0` (the only point of `Euc 0` has norm `0`) and `FDissipation ≡ 0`
(`riccHess ≡ 0`), so `HasDerivAt (fun u => F (E u)) (FDissipation (E t)) t` holds
for **every** `t > 0` — the hypothesis of `fflow_literal_FDerivativeStatement_of_idempotent`
is inhabited.  Together with `fflow_literal_FDerivative_inconsistent` (failure for
`n = 1`) and `fflow_idempotency_iff_zero_dim`, this pins down the literal D7 field
as satisfiable exactly on the degenerate model, while the corrected identity
(`fflow_F_hasDerivAt`) holds on every nontrivial model. -/
theorem fflow_literal_FDerivativeStatement_zero_dim (τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    FDerivativeStatement (fun u => fflowEntropyData 0 τ₀ hτ₀ u) := by
  intro t _ht
  have hF0 : ∀ u : ℝ, (fflowEntropyData 0 τ₀ hτ₀ u).F = 0 := by
    intro u
    simp only [EntropyData.F, fflowEntropyData]
    change ∫ x : Euc 0, (0 + fflowGradSq τ₀ u x) * gaussianKernel 0 τ₀ x ∂volume = 0
    have hfun : (fun x : Euc 0 => (0 + fflowGradSq τ₀ u x) * gaussianKernel 0 τ₀ x)
        = fun _ : Euc 0 => (0 : ℝ) := by
      funext x
      unfold fflowGradSq
      have hx : ‖x‖ ^ 2 = 0 := by
        have hz : x = 0 := Subsingleton.elim x 0
        rw [hz]
        norm_num
      rw [hx]
      norm_num
    rw [hfun, MeasureTheory.integral_zero]
  have hFD0 : EntropyData.FDissipation (fflowEntropyData 0 τ₀ hτ₀ t) = 0 := by
    simp only [EntropyData.FDissipation, fflowEntropyData]
    change ∫ x : Euc 0, 2 * (fflowRiccHess 0 τ₀ t) ^ 2 * gaussianKernel 0 τ₀ x ∂volume = 0
    rw [fflow_riccHess_eq_zero_of_zero_dim τ₀ t]
    have hfun : (fun x : Euc 0 => 2 * (0 : ℝ) ^ 2 * gaussianKernel 0 τ₀ x)
        = fun _ : Euc 0 => (0 : ℝ) := by
      funext x
      norm_num
    rw [hfun, MeasureTheory.integral_zero]
  have hder : HasDerivAt (fun u => (fflowEntropyData 0 τ₀ hτ₀ u).F) (0 : ℝ) t := by
    have hev : (fun u => (fflowEntropyData 0 τ₀ hτ₀ u).F) =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards with u
      exact hF0 u
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  simpa [hFD0] using hder

end

end Poincare.D12.EntropyVariation
