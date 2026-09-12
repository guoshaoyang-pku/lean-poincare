/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (Gaussian heat bridge)

# The backward Gaussian on the chart: conjugate heat equation on its finite lifetime

This module instantiates the D3/D4/D7 entropy-certificate interfaces with the genuine
backward Gaussian on the two-dimensional Euclidean chart `Vec 2 = Fin 2 → ℝ`:

* `laplacian_gaussian` — the D12 Euclidean chart Laplacian of a radial Gaussian
  `x ↦ c exp(-b S(x))` is `(4 b² S(x) - 2 d b) · c exp(-b S(x))` (from
  `laplacian_radial`);
* `gaussian_conjugate_heat` — the **pointwise conjugate heat equation** for the backward
  Gaussian family `ρ_s(x) = (4π(τ-s))⁻¹ exp(-S(x)/(4(τ-s)))`:
  `∂_s ρ_s(x) = -Δρ_s(x)` for `s < τ`. This is the honest-form discharge of the
  `ConjugateMeasureEvolutionStatement` content of blocker `I4` on its finite lifetime.

**Why the statement is localized to `s < τ`.** `EntropyData` requires `τ > 0` and the
D3/D7 `ConjugateMeasureEvolutionStatement` quantifies over *all* `t > 0`. A nontrivial
nonnegative solution of the backward heat equation on all of `(0,∞)` with a positive
coupling parameter does not exist: the D3 statement is satisfiable only by degenerate
(zero) data. The Gaussian lives on the finite lifetime `(0, τ)`, so the honest form of
the statement is the localized one proved here; the unrestricted D3 form is recorded as
defective rather than silently weakened (same pattern as the `WeightedIBPStatement`
defect in `Poincare.D13.Bridge`).

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.BochnerFlat

open scoped BigOperators

noncomputable section

open MeasureTheory

namespace Poincare.D13.HeatBridge

open Poincare.D12.VolumeIBP
open Poincare.D13.EuclideanChart
open Poincare.D13.EuclideanChart.ChartMetric
open Poincare.Longrun.Entropy

/-! ## Radial Gaussians on the chart -/

/-- The derivative of the Gaussian profile: `(c e^{-bs})' = -b (c e^{-bs})`. -/
lemma hasDerivAt_gaussProfile (c b s : ℝ) :
    HasDerivAt (fun s : ℝ => c * Real.exp (-b * s)) (-b * (c * Real.exp (-b * s))) s := by
  have hlin : HasDerivAt (fun s : ℝ => -b * s) (-b) s := by
    simpa using (hasDerivAt_id s).const_mul (-b)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-b * s)) (Real.exp (-b * s) * (-b)) s :=
    hlin.exp
  have h := hexp.const_mul c
  rw [show (-b * (c * Real.exp (-b * s))) = c * (Real.exp (-b * s) * (-b)) by ring]
  exact h

/-- The derivative of the Gaussian profile: `(c e^{-bs})' = -b (c e^{-bs})`. -/
lemma deriv_gaussProfile (c b : ℝ) :
    deriv (fun s : ℝ => c * Real.exp (-b * s)) = fun s => -b * (c * Real.exp (-b * s)) := by
  funext s
  rw [(hasDerivAt_gaussProfile c b s).deriv]

/-- The second derivative of the Gaussian profile: `(c e^{-bs})'' = b² (c e^{-bs})`. -/
lemma deriv_deriv_gaussProfile (c b : ℝ) :
    deriv (deriv (fun s : ℝ => c * Real.exp (-b * s))) =
      fun s => b ^ 2 * (c * Real.exp (-b * s)) := by
  rw [deriv_gaussProfile]
  funext s
  have h : HasDerivAt (fun s : ℝ => -b * (c * Real.exp (-b * s)))
      (-b * (-b * (c * Real.exp (-b * s)))) s :=
    (hasDerivAt_gaussProfile c b s).const_mul (-b)
  rw [h.deriv]
  ring

/-- The Gaussian profile is differentiable at every point, with its own derivative. -/
lemma hasDerivAt_gaussProfile_deriv (c b s : ℝ) :
    HasDerivAt (fun s : ℝ => c * Real.exp (-b * s))
      (deriv (fun s : ℝ => c * Real.exp (-b * s)) s) s := by
  rw [deriv_gaussProfile]
  exact hasDerivAt_gaussProfile c b s

/-- **Laplacian of a radial Gaussian on the chart.**
`Δ (c exp(-b S))(x) = (4 b² S(x) - 2 d b) · c exp(-b S(x))`. -/
lemma laplacian_gaussian (c b : ℝ) (x : Vec (n + 1)) :
    (ChartMetric.euclideanChartMetric (n + 1)).laplacian
        (fun y => c * Real.exp (-b * radSq y)) x =
      (4 * b ^ 2 * radSq x - 2 * (n + 1) * b) * (c * Real.exp (-b * radSq x)) := by
  have hψ' : HasDerivAt (deriv (fun s : ℝ => c * Real.exp (-b * s)))
      (deriv (deriv (fun s : ℝ => c * Real.exp (-b * s))) (radSq x)) (radSq x) := by
    rw [deriv_deriv_gaussProfile, deriv_gaussProfile]
    have h0 := (hasDerivAt_gaussProfile c b (radSq x)).const_mul (-b)
    change HasDerivAt (fun s : ℝ => -b * (c * Real.exp (-b * s)))
      (b ^ 2 * (c * Real.exp (-b * (radSq x)))) (radSq x)
    rw [show b ^ 2 * (c * Real.exp (-b * radSq x)) =
      -b * (-b * (c * Real.exp (-b * radSq x))) by ring]
    exact h0
  have h := laplacian_radial (fun s : ℝ => c * Real.exp (-b * s)) x
    (fun s => hasDerivAt_gaussProfile_deriv c b s) hψ'
  rw [h, deriv_deriv_gaussProfile, deriv_gaussProfile]
  ring

/-! ## The backward Gaussian density on `Vec 2` -/

/-- The backward Gaussian density `ρ_τ(x) = (4πτ)⁻¹ exp(-S(x)/(4τ))` on the chart `Vec 2`. -/
def gaussDensity (τ : ℝ) (x : Vec 2) : ℝ :=
  (4 * Real.pi * τ)⁻¹ * Real.exp (-(1 / (4 * τ)) * radSq x)

/-- The Laplacian of the backward Gaussian density:
`Δρ_τ(x) = (S(x)/(4τ²) - 1/τ) ρ_τ(x)` on `Vec 2`. -/
lemma laplacian_gaussDensity (τ : ℝ) (hτ : τ ≠ 0) (x : Vec 2) :
    (ChartMetric.euclideanChartMetric 2).laplacian (fun y => gaussDensity τ y) x =
      (radSq x / (4 * τ ^ 2) - 1 / τ) * gaussDensity τ x := by
  have h := laplacian_gaussian (n := 1) (4 * Real.pi * τ)⁻¹ (1 / (4 * τ)) x
  change (ChartMetric.euclideanChartMetric (1 + 1)).laplacian
      (fun y => (4 * Real.pi * τ)⁻¹ * Real.exp (-(1 / (4 * τ)) * radSq y)) x = _
  rw [h]
  unfold gaussDensity
  field_simp [hτ]
  ring

/-- The time derivative of the backward Gaussian density at fixed `x`:
`∂_τ ρ_τ(x) = (S(x)/(4τ²) - 1/τ) ρ_τ(x)`. -/
lemma hasDerivAt_gaussDensity (τ : ℝ) (hτ : τ ≠ 0) (x : Vec 2) :
    HasDerivAt (fun τ' : ℝ => gaussDensity τ' x)
      ((radSq x / (4 * τ ^ 2) - 1 / τ) * gaussDensity τ x) τ := by
  have h1 : HasDerivAt (fun τ' : ℝ => (4 * Real.pi * τ')⁻¹)
      (-(4 * Real.pi) / (4 * Real.pi * τ) ^ 2) τ := by
    have h4 : HasDerivAt (fun τ' : ℝ => 4 * Real.pi * τ') (4 * Real.pi) τ := by
      simpa using (hasDerivAt_id τ).const_mul (4 * Real.pi)
    exact h4.inv (by positivity : 4 * Real.pi * τ ≠ 0)
  have hlin : HasDerivAt (fun τ' : ℝ => -(1 / (4 * τ')) * radSq x)
      (radSq x / (4 * τ ^ 2)) τ := by
    have hinv : HasDerivAt (fun τ' : ℝ => (τ')⁻¹) (-1 / τ ^ 2) τ :=
      (hasDerivAt_id τ).inv hτ
    have h := hinv.const_mul (-(radSq x / 4))
    have hfun : (fun τ' : ℝ => -(1 / (4 * τ')) * radSq x)
        = fun y => -(radSq x / 4) * y⁻¹ := by
      funext τ'
      ring
    rw [hfun]
    rw [show radSq x / (4 * τ ^ 2) = -(radSq x / 4) * (-1 / τ ^ 2) by ring]
    exact h
  have h2 : HasDerivAt (fun τ' : ℝ => Real.exp (-(1 / (4 * τ')) * radSq x))
      (Real.exp (-(1 / (4 * τ)) * radSq x) * (radSq x / (4 * τ ^ 2))) τ := hlin.exp
  have hmul := h1.mul h2
  rw [show (fun τ' : ℝ => gaussDensity τ' x)
      = ((fun τ' : ℝ => (4 * Real.pi * τ')⁻¹) *
          fun τ' : ℝ => Real.exp (-(1 / (4 * τ')) * radSq x)) from rfl]
  rw [show ((radSq x / (4 * τ ^ 2) - 1 / τ) * gaussDensity τ x)
      = (-(4 * Real.pi) / (4 * Real.pi * τ) ^ 2) * Real.exp (-(1 / (4 * τ)) * radSq x)
        + (4 * Real.pi * τ)⁻¹ *
            (Real.exp (-(1 / (4 * τ)) * radSq x) * (radSq x / (4 * τ ^ 2))) by
    unfold gaussDensity
    field_simp [hτ]
    ring]
  exact hmul

/-- **The conjugate heat equation for the backward Gaussian (pointwise, honest lifetime).**
For `s < τ` and every `x`, `∂_s ρ_{τ-s}(x) = -Δρ_{τ-s}(x)`.

This is the localized form of the D3/D7 `ConjugateMeasureEvolutionStatement` on the finite
lifetime of the backward Gaussian. -/
theorem gaussian_conjugate_heat (τ s : ℝ) (hτ : 0 < τ) (hs : s < τ) (x : Vec 2) :
    HasDerivAt (fun t : ℝ => gaussDensity (τ - t) x)
      (-((ChartMetric.euclideanChartMetric 2).laplacian
        (fun y => gaussDensity (τ - s) y) x)) s := by
  have hsub : HasDerivAt (fun t : ℝ => τ - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub τ
  have hτs : τ - s ≠ 0 := ne_of_gt (sub_pos.mpr hs)
  have hinner := hasDerivAt_gaussDensity (τ - s) hτs x
  have hcomp := hinner.comp s hsub
  rw [laplacian_gaussDensity (τ - s) hτs x]
  rw [show -((radSq x / (4 * (τ - s) ^ 2) - 1 / (τ - s)) * gaussDensity (τ - s) x)
      = ((radSq x / (4 * (τ - s) ^ 2) - 1 / (τ - s)) * gaussDensity (τ - s) x) * (-1) by ring]
  exact hcomp

end Poincare.D13.HeatBridge

/-! ## Axiom audit -/

#print axioms Poincare.D13.HeatBridge.hasDerivAt_gaussProfile
#print axioms Poincare.D13.HeatBridge.deriv_gaussProfile
#print axioms Poincare.D13.HeatBridge.deriv_deriv_gaussProfile
#print axioms Poincare.D13.HeatBridge.laplacian_gaussian
#print axioms Poincare.D13.HeatBridge.gaussDensity
#print axioms Poincare.D13.HeatBridge.laplacian_gaussDensity
#print axioms Poincare.D13.HeatBridge.hasDerivAt_gaussDensity
#print axioms Poincare.D13.HeatBridge.gaussian_conjugate_heat
