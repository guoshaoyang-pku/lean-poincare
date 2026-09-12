/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-deturck-shorttime-producer)
-/

import Mathlib
import Poincare.D12.ParabolicLocal.GaussianSetup
import Poincare.D13.DeturckProducer.PicardModel

/-!
# Poincare.D13.DeturckProducer.FlatInstance

**The flat instance: the producer output on the flat metric is the D12 Gaussian setup.**

On the flat background `flatSmoothMetric n` the linearized DeTurck operator is the rough
Laplacian, whose evolution family on the spatial Banach space `BUCn n` of bounded
uniformly continuous functions on `ℝⁿ` is the D12 Gaussian heat semigroup
(`Poincare.D12.ParabolicLocal.gaussianSetup`).  This file shows the produced model is
**literally** the D12 setup:

* `flatPicardModel` — the produced `RicciDeTurckPicardModel` on the flat metric with the
  Gaussian semigroup and a given globally Lipschitz reaction `F`;
* `flatPicardModel_duhamel_eq_gaussianSetup` — the model's Duhamel data is definitionally
  the D12 `gaussianSetup`;
* `flatPicardModel_mildSolution_eq_heatMildSolution` — the mild solution produced from the
  flat model is exactly the D12 `heatMildSolution` (the constructed downstream checked use
  of the D12 deliverable);
* `flatPicardModel_duhamelMap_eq_gaussianSetup` — the Duhamel maps coincide;
* `flatCertificate_positive` — the flat model's strict-parabolicity certificate is the
  general `producerStrictParabolic` instantiated on the flat metric, i.e. the produced
  certificate for the flat instance.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open scoped BigOperators
open scoped Matrix
open scoped NNReal
open scoped BoundedContinuousFunction

set_option linter.unusedSimpArgs false

namespace Poincare
namespace D13
namespace DeturckProducer

noncomputable section

namespace FlatInstance

open Poincare.D12.ParabolicLocal
open Poincare.D13.ToppingAdapter.Scalar
open Set
open DeturckProducer.PicardModel
open DeturckProducer.SmoothMetricData
open DeturckProducer.SymbolMatrix

variable {n : ℕ}

/-- **The flat instance of the producer**: the produced model on the flat metric
`flatSmoothMetric n` with the D12 Gaussian heat semigroup `gaussianS n`, a globally
Lipschitz reaction `F` and an initial datum `u₀`.  The strict-parabolicity certificate is
the general `producerStrictParabolic` on the flat metric (all uniform bounds explicit:
`lower = 1/2`, `upper = 2`). -/
def flatPicardModel (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n) (hF : LipschitzWith L F)
    (u₀ : BUCn n) : RicciDeTurckPicardModel n (BUCn n) L :=
  RicciDeTurckPicardModel.of_metric (flatSmoothMetric n) (gaussianS n) F u₀
    (gaussianSetup n F hF u₀) (by intro t; rfl) rfl rfl

/-- **The flat model's Duhamel data is the D12 Gaussian setup** (definitionally). -/
theorem flatPicardModel_duhamel_eq_gaussianSetup (n : ℕ) {L : ℝ≥0}
    (F : BUCn n → BUCn n) (hF : LipschitzWith L F) (u₀ : BUCn n) :
    (flatPicardModel n F hF u₀).duhamel = gaussianSetup n F hF u₀ := rfl

/-- The flat model's Duhamel map is the Gaussian setup's Duhamel map. -/
theorem flatPicardModel_duhamelMap_eq_gaussianSetup (n : ℕ) {L : ℝ≥0}
    (F : BUCn n → BUCn n) (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T) :
    (flatPicardModel n F hF u₀).duhamel.duhamelMap T hT =
      (gaussianSetup n F hF u₀).duhamelMap T hT := by
  rw [flatPicardModel_duhamel_eq_gaussianSetup]

/-- **Short-time existence and uniqueness of the mild solution from the flat model** —
literally the D12 `existsUnique_heatMildSolution`, through the produced model. -/
theorem existsUnique_mildSolution_of_flatModel (n : ℕ) {L : ℝ≥0}
    (F : BUCn n → BUCn n) (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T)
    (hK : (1 : ℝ) * L * T < 1) :
    ∃! u : DuhamelSetup.SolutionSpace (BUCn n) T,
      (flatPicardModel n F hF u₀).duhamel.duhamelMap T hT u = u :=
  (flatPicardModel n F hF u₀).existsUnique_mildSolution_of_model hT hK

/-- The mild solution produced from the flat model. -/
def flatMildSolution (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n) (hF : LipschitzWith L F)
    (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T) (hK : (1 : ℝ) * L * T < 1) :
    DuhamelSetup.SolutionSpace (BUCn n) T :=
  (flatPicardModel n F hF u₀).mildSolution_of_model hT hK

/-- **The flat model's mild solution is exactly the D12 `heatMildSolution`**: the
constructed downstream checked use of the D12 deliverable through the produced model. -/
theorem flatMildSolution_eq_heatMildSolution (n : ℕ) {L : ℝ≥0}
    (F : BUCn n → BUCn n) (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T)
    (hK : (1 : ℝ) * L * T < 1) :
    flatMildSolution n F hF u₀ hT hK = heatMildSolution n F hF u₀ hT hK := by
  unfold flatMildSolution RicciDeTurckPicardModel.mildSolution_of_model heatMildSolution
  rfl

/-- The flat model's mild solution satisfies the Duhamel identity of the semilinear heat
equation with the Gaussian semigroup (the D12 kernel-form statement). -/
theorem flatMildSolution_duhamel_eq (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T)
    (hK : (1 : ℝ) * L * T < 1) (t : Icc (0 : ℝ) T) :
    (flatMildSolution n F hF u₀ hT hK) t = gaussianS n t u₀ +
      ∫ s in (0 : ℝ)..t, gaussianS n (t - s)
        (F ((DuhamelSetup.extendToInterval T hT (flatMildSolution n F hF u₀ hT hK)) s)) := by
  have h := (flatPicardModel n F hF u₀).mildSolution_of_model_duhamel_eq hT hK t
  unfold flatMildSolution
  rw [h]
  simp only [flatPicardModel, RicciDeTurckPicardModel.of_metric, gaussianSetup]

/-- The flat model's mild solution attains the initial datum at time zero:
`u(0) = u₀` (the Gaussian semigroup at time zero is the identity). -/
theorem flatMildSolution_initial (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T)
    (hK : (1 : ℝ) * L * T < 1) :
    (flatMildSolution n F hF u₀ hT hK) ⟨(0 : ℝ), ⟨le_rfl, hT⟩⟩ = u₀ := by
  rw [flatMildSolution_eq_heatMildSolution]
  rw [heatMildSolution_initial]

/-- **The flat model's strict-parabolicity certificate**: the produced certificate on the
flat instance is the general `producerStrictParabolic` for the flat metric — at every
point, every nonzero covector and every nonzero metric direction, the pairing with the
DeTurck linearization symbol is strictly positive. -/
theorem flatCertificate_positive (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) (x ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    (h : Matrix (Fin n) (Fin n) ℝ) (hh : h ≠ 0) :
    0 < bilinPairingMat h ((flatPicardModel n F hF u₀).principalSymbol x ξ h) := by
  simp only [flatPicardModel, RicciDeTurckPicardModel.of_metric]
  exact (flatSmoothMetric n).producerStrictParabolic x hξ h hh

/-- The Euclidean squared norm equals the self-dot-product (used below). -/
theorem euclideanNormSq_eq_dotProduct (n : ℕ) (ξ : Fin n → ℝ) :
    euclideanNormSq ξ = dotProduct ξ ξ := by
  simp only [euclideanNormSq, dotProduct, pow_two]

/-- The inverse of the identity matrix acts as the identity on vectors. -/
theorem one_inv_mulVec (n : ℕ) (ξ : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ)⁻¹ *ᵥ ξ = ξ := by
  have hunit : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ).det) := by
    simpa using (isUnit_one : IsUnit (1 : ℝ))
  calc
    (1 : Matrix (Fin n) (Fin n) ℝ)⁻¹ *ᵥ ξ =
        (1 : Matrix (Fin n) (Fin n) ℝ)⁻¹ *ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ ξ) := by
      rw [Matrix.one_mulVec]
    _ = ((1 : Matrix (Fin n) (Fin n) ℝ)⁻¹ * 1) *ᵥ ξ := by rw [← Matrix.mulVec_mulVec]
    _ = 1 *ᵥ ξ := by rw [Matrix.nonsing_inv_mul 1 hunit]
    _ = ξ := by rw [Matrix.one_mulVec]

/-- **The flat metric's DeTurck linearization symbol equals the Euclidean norm squared
times the direction** — the produced certificate's symbol is exactly the D13
`localDeTurckStrictParabolic` pairing object: on the flat metric the symbol is
`|ξ|² · h`. -/
theorem flatDeTurckLinSymbol_eq_euclideanNormSq_smul (n : ℕ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) :
    deTurckLinSymbolMat ((flatSmoothMetric n).g 0) ξ h =
      (euclideanNormSq ξ) • h := by
  rw [deTurckLinSymbolMat_eq_smul]
  change covectorNormSqMat ((flatSmoothMetric n).g 0) ξ • h = euclideanNormSq ξ • h
  congr 1
  rw [covectorNormSqMat]
  simp only [flatSmoothMetric]
  rw [one_inv_mulVec]
  exact (euclideanNormSq_eq_dotProduct n ξ).symm

end FlatInstance

end

end DeturckProducer
end D13
end Poincare
