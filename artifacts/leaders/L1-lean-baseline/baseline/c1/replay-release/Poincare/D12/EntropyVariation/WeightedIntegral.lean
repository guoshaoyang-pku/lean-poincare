/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-entropy-variation)

# Differentiation of time-dependent weighted integrals

This is the **missing analytic step** named `B-D7-F-DERIVATIVE` in the D7 ledger:
differentiation under the integral sign for a genuine integral functional whose
integrand *and* weight both depend on time,

`t ↦ ∫ x, g t x * ρ t x ∂μ`,

with all integrability and domination obligations explicit.  The main theorem
`hasDerivAt_weightedIntegral` is proved here unconditionally from mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` (file
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`); nothing is assumed about
the data beyond the listed regularity, measurability and domination hypotheses.
The time-dependent-measure obligation appears as the weight derivative `ρ'`;
setting it to zero gives the fixed-measure (Perelman `F`-flow) case.

Every hypothesis is an explicit field of the statement, and the theorem also
returns integrability of the derivative combination, which is exactly the
integrability obligation needed to iterate the rule (e.g. for the fourth-moment
identity of the Gaussian model).

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory TopologicalSpace Filter Set
open scoped Topology Filter

namespace Poincare.D12.EntropyVariation

universe u

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- **Differentiation of a time-dependent weighted integral.**

`t ↦ ∫ x, g t x * ρ t x ∂μ` is differentiable at `t₀` with derivative
`∫ x, g' t₀ x * ρ t₀ x + g t₀ x * ρ' t₀ x ∂μ` provided:

* on a neighbourhood `s` of `t₀` (the same neighbourhood for all `x`), the functions
  `t ↦ g t x` and `t ↦ ρ t x` are differentiable for `μ`-a.e. `x`, with derivatives
  `g' t x` and `ρ' t x` (`hderiv_g`, `hderiv_ρ`);
* the derivative combination `g' t x * ρ t x + g t x * ρ' t x` is pointwise dominated
  on `s` by the integrable function `bound`, uniformly in `t ∈ s` (`hdom`, `hbound`);
* the integrand `x ↦ g t₀ x * ρ t₀ x` is integrable (`hint`);
* the measurability side conditions hold (`hmeas`, `hmeas'`).

The conclusion is the pair: integrability of the derivative combination, and the
derivative formula.  The weight `ρ` plays the role of the density of the
time-dependent measure `dm_t = ρ t dμ`; the term `g t x * ρ' t x` is the
measure-evolution contribution. -/
theorem hasDerivAt_weightedIntegral {g ρ g' ρ' : ℝ → X → ℝ} {bound : X → ℝ}
    {t₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀)
    (hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun x => g t x * ρ t x) μ)
    (hint : Integrable (fun x => g t₀ x * ρ t₀ x) μ)
    (hmeas' : AEStronglyMeasurable (fun x => g' t₀ x * ρ t₀ x + g t₀ x * ρ' t₀ x) μ)
    (hderiv_g : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun u => g u x) (g' t x) t)
    (hderiv_ρ : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun u => ρ u x) (ρ' t x) t)
    (hdom : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖g' t x * ρ t x + g t x * ρ' t x‖ ≤ bound x)
    (hbound : Integrable bound μ) :
    Integrable (fun x => g' t₀ x * ρ t₀ x + g t₀ x * ρ' t₀ x) μ ∧
      HasDerivAt (fun t => ∫ x, g t x * ρ t x ∂μ)
        (∫ x, g' t₀ x * ρ t₀ x + g t₀ x * ρ' t₀ x ∂μ) t₀ := by
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ s,
      HasDerivAt (fun u => g u x * ρ u x) (g' t x * ρ t x + g t x * ρ' t x) t := by
    filter_upwards [hderiv_g, hderiv_ρ] with x hg hr t ht
    exact (hg t ht).mul (hr t ht)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => g t x * ρ t x) (s := s) (x₀ := t₀) hs hmeas hint
    (F' := fun t x => g' t x * ρ t x + g t x * ρ' t x) hmeas' hdom hbound hdiff
  exact hmain

/-- **Special case: fixed measure.**  When the weight does not depend on time
(`ρ t x = ρ x`), the measure-evolution term vanishes and
`t ↦ ∫ x, g t x * ρ x ∂μ` has derivative `∫ x, g' t₀ x * ρ x ∂μ`. -/
theorem hasDerivAt_weightedIntegral_constWeight {g g' : ℝ → X → ℝ} {ρ : X → ℝ}
    {bound : X → ℝ} {t₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀)
    (hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun x => g t x * ρ x) μ)
    (hint : Integrable (fun x => g t₀ x * ρ x) μ)
    (hmeas' : AEStronglyMeasurable (fun x => g' t₀ x * ρ x) μ)
    (hderiv_g : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun u => g u x) (g' t x) t)
    (hdom : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖g' t x * ρ x‖ ≤ bound x)
    (hbound : Integrable bound μ) :
    Integrable (fun x => g' t₀ x * ρ x) μ ∧
      HasDerivAt (fun t => ∫ x, g t x * ρ x ∂μ) (∫ x, g' t₀ x * ρ x ∂μ) t₀ := by
  have hderiv_ρ : ∀ᵐ x ∂μ, ∀ t ∈ s,
      HasDerivAt (fun u => ρ x) (0 : ℝ) t := by
    filter_upwards with x t ht
    exact hasDerivAt_const t (ρ x)
  have hmeas'' : AEStronglyMeasurable (fun x => g' t₀ x * ρ x + g t₀ x * (0 : ℝ)) μ := by
    simpa using hmeas'
  have hdom1 : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖g' t x * ρ x + g t x * (0 : ℝ)‖ ≤ bound x := by
    filter_upwards [hdom] with x hx t ht
    simpa using hx t ht
  have hmain := hasDerivAt_weightedIntegral (ρ := fun _ => ρ) (ρ' := fun _ _ => (0 : ℝ))
    hs hmeas hint hmeas'' hderiv_g hderiv_ρ hdom1 hbound
  have hder : (∫ x, g' t₀ x * ρ x + g t₀ x * (0 : ℝ) ∂μ) = ∫ x, g' t₀ x * ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  refine ⟨by simpa using hmain.1, ?_⟩
  simpa [hder] using hmain.2

/-- **Special case: unweighted parametric integral.**  With `ρ ≡ 1`,
`t ↦ ∫ x, g t x ∂μ` has derivative `∫ x, g' t₀ x ∂μ`. -/
theorem hasDerivAt_integral_param {g g' : ℝ → X → ℝ} {bound : X → ℝ}
    {t₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀)
    (hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (g t) μ)
    (hint : Integrable (g t₀) μ)
    (hmeas' : AEStronglyMeasurable (g' t₀) μ)
    (hderiv_g : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun u => g u x) (g' t x) t)
    (hdom : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖g' t x‖ ≤ bound x)
    (hbound : Integrable bound μ) :
    Integrable (g' t₀) μ ∧ HasDerivAt (fun t => ∫ x, g t x ∂μ) (∫ x, g' t₀ x ∂μ) t₀ := by
  have hmeas1 : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun x => g t x * (1 : ℝ)) μ := by
    filter_upwards [hmeas] with t ht
    simpa using ht
  have hint1 : Integrable (fun x => g t₀ x * (1 : ℝ)) μ := by simpa using hint
  have hmeas1' : AEStronglyMeasurable (fun x => g' t₀ x * (1 : ℝ) + g t₀ x * (0 : ℝ)) μ := by
    simpa using hmeas'
  have hderiv_ρ : ∀ᵐ x ∂μ, ∀ t ∈ s,
      HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) t := by
    filter_upwards with x t ht
    exact hasDerivAt_const t (1 : ℝ)
  have hdom1 : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖g' t x * (1 : ℝ) + g t x * (0 : ℝ)‖ ≤ bound x := by
    filter_upwards [hdom] with x hx t ht
    simpa using hx t ht
  have hmain := hasDerivAt_weightedIntegral (ρ := fun _ _ => (1 : ℝ)) (ρ' := fun _ _ => 0)
    hs hmeas1 hint1 hmeas1' hderiv_g hderiv_ρ hdom1 hbound
  have hfun : (fun t => ∫ x, g t x * (1 : ℝ) ∂μ) = fun t => ∫ x, g t x ∂μ := by
    funext t
    apply integral_congr_ae
    filter_upwards with x
    simp
  have hder : (∫ x, g' t₀ x * (1 : ℝ) + g t₀ x * (0 : ℝ) ∂μ) = ∫ x, g' t₀ x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  refine ⟨by simpa using hmain.1, ?_⟩
  have h2 : HasDerivAt (fun t => ∫ x, g t x * (1 : ℝ) ∂μ)
      (∫ x, g' t₀ x * (1 : ℝ) + g t₀ x * (0 : ℝ) ∂μ) t₀ := hmain.2
  rw [hfun, hder] at h2
  exact h2

end Poincare.D12.EntropyVariation
