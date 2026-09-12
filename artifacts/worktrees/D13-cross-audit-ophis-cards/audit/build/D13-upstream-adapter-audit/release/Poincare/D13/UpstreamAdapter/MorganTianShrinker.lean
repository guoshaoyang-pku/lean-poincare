/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-upstream-adapter-audit)

# Upstream adapter: MorganTian gradient-shrinker equation ↔ local D12 Gaussian shrinker

This file is part of the D13 upstream-adapter audit.  It transcribes the gradient
shrinking-soliton equation of the pinned Frenzymath snapshot (package `MorganTian`,
`formalized-sources/MorganTian/MorganTianLib/Ch03/RicciFlow/Soliton.lean`, commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0) in its Euclidean (flat) form and
proves that the local D12 Gaussian shrinker satisfies it.

Upstream declarations (quoted from the snapshot):
* `MorganTianLib.IsSolitonGenerator` (Soliton.lean:109):
  `-Ric(g) = (1/2) L_X g - lambda g`;
* `MorganTianLib.metricLieDerivativeAt_gradientField` (Soliton.lean:124, theorem):
  `L_(grad f) g = 2 Hess_g f`;
* `MorganTianLib.IsGradientShrinkerPotential` (Soliton.lean:183): the (GSS) equation
  `-Ric(g) = Hess_g f - lambda g` with `0 < lambda`;
* `MorganTianLib.IsGradientShrinkerPotential.isSolitonGenerator` (Soliton.lean:199,
  theorem): (GSS) implies the soliton-generator equation for the gradient field;
* `MorganTianLib.solitonScale` (Soliton.lean:239): `sigma(t) = 1 - 2 lambda t`.

The upstream types live on a general manifold with model `I` (`RiemannianMetric I M`,
`TangentSpace I p`, `SmoothVectorField I M`); those are not importable into the local
release package (different toolchain and no upstream build).  The Euclidean transcription
below is the flat-model instantiation, field by field:
`ricciTensorAt = 0` (flat), `hessianAt = iteratedFDeriv ℝ 2` (D12 convention),
`g.metricInner = ⟪·, ·⟫_ℝ`, and the gradient field is the Riesz lift
`(innerCLM (Euc n)).symm ∘ fderiv`.

Classification: the transcribed predicates are interface definitions (upstream source
claims with the exact file/line); the model theorems (`*_shrinkerFpot*`,
`*_shrinkGrad*`) are local proved theorems on the explicit flat Gaussian model; the
conditional implication `isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean`
is a conditional adapter with the upstream gradient/Lie-derivative identity as its
explicit hypothesis.
-/

import Poincare.D12.EntropyVariation.GaussianShrinker
import Poincare.D12.EntropyVariation.FFlowModel
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Poincare.D13.UpstreamAdapter.MorganTian

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## 1. Transcribed upstream definitions (Euclidean form) -/

/-- Upstream `MorganTianLib.solitonScale` (Soliton.lean:239): `sigma(t) = 1 - 2 lambda t`.
Transcribed verbatim. -/
def solitonScale (lambda t : ℝ) : ℝ :=
  1 - 2 * lambda * t

/-- The upstream Lie derivative of the metric (Soliton.lean:85) in its flat Euclidean
form: `L_X g (v,w) = ⟨DX(x)[v], w⟩ + ⟨v, DX(x)[w]⟩` (the two metric-compatibility terms;
on the flat model there is no connection contribution). -/
noncomputable def metricLieDerivativeFlat {n : ℕ} (X : Euc n → Euc n)
    (x v w : Euc n) : ℝ :=
  ⟪fderiv ℝ X x v, w⟫_ℝ + ⟪v, fderiv ℝ X x w⟫_ℝ

/-- The **gradient field of the shrinker potential** (upstream `gradientField g f hf`,
Soliton.lean, in its Euclidean form): for `f = ‖x‖²/(4τ)` the gradient is the explicit field
`x ↦ (1/(2τ)) • x`.  Rather than postulating a Riesz lift, the defining gradient
characterization `⟪X x, w⟫ = fderiv f x w` is proved below
(`shrinkerGradientField_isGradient`). -/
noncomputable def shrinkerGradientField (n : ℕ) (τ : ℝ) : Euc n → Euc n :=
  fun x => (1 / (2 * τ)) • x

/-- Upstream `MorganTianLib.IsSolitonGenerator` (Soliton.lean:109),
Euclidean transcription: `-Ric = (1/2) L_X g - lambda g` with the flat Ricci tensor
`ricciEuclidean = 0`. -/
noncomputable def IsSolitonGeneratorEuclidean (n : ℕ) (X : Euc n → Euc n)
    (lambda : ℝ) : Prop :=
  ∀ x v w, -(0 : ℝ) = (1 / 2 : ℝ) * metricLieDerivativeFlat X x v w -
    lambda * ⟪v, w⟫_ℝ

/-- Upstream `MorganTianLib.IsGradientShrinkerPotential` (Soliton.lean:183),
Euclidean transcription: the (GSS) equation `-Ric = Hess f - lambda g` with `ContDiff ∞`
and `0 < lambda`, on the flat model. -/
noncomputable def IsGradientShrinkerPotentialEuclidean (n : ℕ) (f : Euc n → ℝ)
    (lambda : ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ 0 < lambda ∧
    ∀ x v w, -(0 : ℝ) = iteratedFDeriv ℝ 2 f x ![v, w] - lambda * ⟪v, w⟫_ℝ

/-! ## 2. Model theorems: the local D12 Gaussian shrinker satisfies the upstream equations -/

/-- **Scale correspondence.**  The upstream soliton scale at `lambda = 1/(2τ₀)` is exactly
the local D12 F-flow metric scale `fflowMetricScale τ₀ t = 1 - t/τ₀`
(`FFlowModel.lean:80`), for every real `t` (including the degenerate `τ₀ = 0` case).
Class: local proved theorem (definitional correspondence of the two scales). -/
theorem solitonScale_eq_fflowMetricScale (τ₀ t : ℝ) :
    solitonScale (1 / (2 * τ₀)) t = Poincare.D12.EntropyVariation.fflowMetricScale τ₀ t := by
  unfold solitonScale Poincare.D12.EntropyVariation.fflowMetricScale
  by_cases h : τ₀ = 0
  · simp [h]
  · field_simp [h]

/-- **Gradient characterization of the shrinker gradient field.**  The explicit field
`x ↦ (1/(2τ)) • x` satisfies the defining equation of the gradient of `f = ‖x‖²/(4τ)`:
`⟪X x, w⟫ = fderiv f x w` for every direction `w`.  The derivative is the D12 Fréchet
identity `hasFDerivAt_shrinkerFpot`; the Riesz side is the local D10 `innerCLM_apply`.
Class: local proved theorem (model computation). -/
theorem shrinkerGradientField_isGradient (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (x w : Euc n) :
    ⟪shrinkerGradientField n τ x, w⟫_ℝ =
      fderiv ℝ (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) x w := by
  unfold shrinkerGradientField
  have hfder : fderiv ℝ (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) x =
      (1 / (2 * τ)) • (Poincare.D10.HeatKernelEuclidean.innerCLM (Euc n)) x :=
    (Poincare.D12.EntropyVariation.hasFDerivAt_shrinkerFpot τ hτ x).fderiv
  rw [hfder]
  simp [Poincare.D10.HeatKernelEuclidean.innerCLM_apply, real_inner_smul_left]

/-- **Derivative of the shrinker gradient field.**  The derivative of `x ↦ (1/(2τ)) • x`
is the constant linear map `(1/(2τ)) • id`.  Class: local proved theorem (elementary). -/
theorem fderiv_shrinkerGrad (n : ℕ) {τ : ℝ} :
    fderiv ℝ (fun x : Euc n => (1 / (2 * τ)) • x) =
      fun _ : Euc n => (1 / (2 * τ)) • (ContinuousLinearMap.id ℝ (Euc n)) := by
  funext x
  exact ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.id ℝ (Euc n))).const_smul
    (1 / (2 * τ))).fderiv

/-- **Lie derivative of the shrinker gradient field.**  On the flat model with
`X = grad f` for the shrinker potential, `L_X g (v,w) = (1/τ) ⟪v, w⟫`, i.e. exactly
`2 * Hess f (v,w)` by the D12 Hessian identity `iteratedFDeriv_two_shrinkerFpot`.
This is the model instance of the upstream theorem `metricLieDerivativeAt_gradientField`
(Soliton.lean:124).  Class: local proved theorem (model computation). -/
theorem metricLieDerivativeFlat_shrinkerGrad (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0)
    (x v w : Euc n) :
    metricLieDerivativeFlat (shrinkerGradientField n τ) x v w
      = (1 / τ) * ⟪v, w⟫_ℝ := by
  unfold metricLieDerivativeFlat shrinkerGradientField
  rw [fderiv_shrinkerGrad n]
  simp only [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
    real_inner_smul_right]
  field_simp [hτ]
  ring

/-- **The (GSS) equation on the shrinker.**  The upstream gradient-shrinker equation
`-Ric = Hess f - lambda g` holds on the flat Gaussian model for the potential
`f = ‖x‖²/(4τ)` with `lambda = 1/(2τ)` and `Ric = 0`: by the D12 Hessian identity the
right side is `(1/(2τ))⟪v,w⟫ - (1/(2τ))⟪v,w⟫ = 0 = -Ric`.  This is the Euclidean instance
of upstream `IsGradientShrinkerPotential` (Soliton.lean:183) and the geometric half of
the local D12 shrinker model (`GaussianShrinker.lean`).  Class: local proved theorem
(model theorem, nontrivial: the D12 Hessian identity is consumed). -/
theorem shrinkerFpot_isGradientShrinkerPotentialEuclidean (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IsGradientShrinkerPotentialEuclidean n (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ))
      (1 / (2 * τ)) := by
  unfold IsGradientShrinkerPotentialEuclidean
  constructor
  · exact (contDiff_norm_sq ℝ (E := Euc n)).div_const (4 * τ)
  constructor
  · positivity
  · intro x v w
    rw [Poincare.D12.EntropyVariation.iteratedFDeriv_two_shrinkerFpot τ (ne_of_gt hτ)]
    ring

/-- **The soliton-generator equation on the shrinker.**  With the gradient field of the
shrinker potential, `-Ric = (1/2) L_X g - lambda g` holds on the flat model with
`lambda = 1/(2τ)`: the Lie-derivative computation above gives `L_X g = (1/τ) g = 2 lambda g`,
so the right side vanishes.  This is the Euclidean instance of upstream
`IsSolitonGenerator` (Soliton.lean:109).  Class: local proved theorem (model theorem). -/
theorem shrinkerGrad_isSolitonGeneratorEuclidean (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IsSolitonGeneratorEuclidean n (shrinkerGradientField n τ)
      (1 / (2 * τ)) := by
  unfold IsSolitonGeneratorEuclidean
  intro x v w
  rw [metricLieDerivativeFlat_shrinkerGrad n (ne_of_gt hτ)]
  simp only [neg_zero]
  field_simp [ne_of_gt hτ]
  ring

/-! ## 3. The upstream GSS → soliton-generator implication (Euclidean transcription) -/

/-- **Upstream `IsGradientShrinkerPotential.isSolitonGenerator` (Soliton.lean:199),
Euclidean transcription.**  If the (GSS) equation `-Ric = Hess f - lambda g` holds and the
gradient field satisfies the upstream Lie-derivative identity
`L_(grad f) g = 2 Hess_g f` (upstream theorem `metricLieDerivativeAt_gradientField`,
Soliton.lean:124), then the soliton-generator equation holds for the gradient field.
The Lie-derivative identity is exposed as the explicit hypothesis `hgradLie` because it is
a theorem upstream (not a definition); on the flat shrinker it is discharged by
`metricLieDerivativeFlat_shrinkerGrad` above.  Class: conditional adapter (typed
implication with the upstream identity as hypothesis). -/
theorem isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean {n : ℕ}
    {X : Euc n → Euc n} {f : Euc n → ℝ} {lambda : ℝ}
    (hgradLie : ∀ x v w,
      metricLieDerivativeFlat X x v w = 2 * iteratedFDeriv ℝ 2 f x ![v, w])
    (h : IsGradientShrinkerPotentialEuclidean n f lambda) :
    IsSolitonGeneratorEuclidean n X lambda := by
  unfold IsSolitonGeneratorEuclidean
  intro x v w
  rw [hgradLie, h.2.2 x v w]
  ring

/-- **The upstream GSS → soliton-generator chain on the shrinker.**  The model instance of
the conditional adapter: the (GSS) theorem and the gradient Lie-derivative computation
together produce the soliton-generator equation for the shrinker gradient field.  Class:
local proved theorem (model theorem; downstream use of both model computations). -/
theorem shrinkerFpot_GSS_and_solitonGenerator (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IsGradientShrinkerPotentialEuclidean n (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ))
        (1 / (2 * τ)) ∧
      IsSolitonGeneratorEuclidean n (shrinkerGradientField n τ)
        (1 / (2 * τ)) := by
  refine ⟨shrinkerFpot_isGradientShrinkerPotentialEuclidean n hτ, ?_⟩
  exact isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean
    (X := shrinkerGradientField n τ) (f := fun y : Euc n => ‖y‖ ^ 2 / (4 * τ))
    (lambda := 1 / (2 * τ))
    (by
      intro x v w
      have hLie := metricLieDerivativeFlat_shrinkerGrad n (ne_of_gt hτ) x v w
      have hHess := Poincare.D12.EntropyVariation.iteratedFDeriv_two_shrinkerFpot τ
        (ne_of_gt hτ) x v w
      rw [hLie, hHess]
      field_simp [ne_of_gt hτ])
    (shrinkerFpot_isGradientShrinkerPotentialEuclidean n hτ)

end Poincare.D13.UpstreamAdapter.MorganTian
