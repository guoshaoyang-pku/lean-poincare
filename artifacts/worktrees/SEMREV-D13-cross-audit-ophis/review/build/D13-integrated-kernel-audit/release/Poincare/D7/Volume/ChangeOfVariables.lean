/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Poincare.D7.Volume.Scaling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Volume.ChangeOfVariables

**D7 orientability and volume-form algebra layer, part 3: the finite-dimensional
change-of-variables lemma for linear maps with nonzero determinant.**

Two layers are proved, both kernel-checked:

* **Algebraic (volume-form) layer** — `VolumeFormData.volumeForm_comp_linearMap`: for a linear
  endomorphism `T` of the inner product space,
  `vol (T ∘ v) = det T * vol v`
  for every frame `v`. This is the determinant change-of-variables rule for top forms, obtained
  from the explicit determinant interface (`volumeForm_eq_det`) and mathlib's
  `Module.Basis.det_comp`.

* **Measure-theoretic layer** — the finite-dimensional linear change of variables for a Haar
  measure `μ` on a finite-dimensional real normed space:
  `∫⁻ x, g (T x) ∂μ = ‖det T‖⁻¹ * ∫⁻ y, g y ∂μ` for `LinearMap.det T ≠ 0`
  (`lintegral_comp_linearMap_eq`), and the inverse form
  `∫⁻ y, g y ∂μ = ‖det T‖ * ∫⁻ x, g (T x) ∂μ` (`lintegral_linearMap_eq`). These are proved from
  mathlib's `Measure.map_linearMap_addHaar_eq_smul_addHaar`; the preimage and image measure
  versions are recorded as corollaries (`addHaar_preimage_linearMap'`,
  `addHaar_image_linearMap'`).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace Poincare.D7.Volume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace VolumeFormData

variable (D : VolumeFormData V)

/-- **The algebraic change-of-variables rule for the volume form.** For a linear endomorphism `T`
of the oriented inner product space and any frame `v`, the volume form of the image frame is the
determinant of `T` times the volume form of `v`. This is the determinant interface
(`volumeForm_eq_det`) combined with `Module.Basis.det_comp`. -/
theorem volumeForm_comp_linearMap (b : OrthonormalBasis (Fin D.n) ℝ V)
    (hb : b.toBasis.orientation = D.orientation) (T : V →ₗ[ℝ] V) (v : Fin D.n → V) :
    D.volumeForm (T ∘ v) = LinearMap.det T * D.volumeForm v := by
  rw [D.volumeForm_eq_det b hb, Module.Basis.det_comp]

/-- The volume form of the image frame under a linear endomorphism is nonzero for every frame with
nonzero volume and every invertible `T`. -/
theorem volumeForm_comp_linearMap_ne_zero (b : OrthonormalBasis (Fin D.n) ℝ V)
    (hb : b.toBasis.orientation = D.orientation) {T : V →ₗ[ℝ] V} (hT : LinearMap.det T ≠ 0)
    {v : Fin D.n → V} (hv : D.volumeForm v ≠ 0) :
    D.volumeForm (T ∘ v) ≠ 0 := by
  rw [D.volumeForm_comp_linearMap b hb]
  exact mul_ne_zero hT hv

end VolumeFormData

/-! ## Measure-theoretic change of variables -/

/-- **The finite-dimensional linear change of variables.** For a Haar measure `μ` on a
finite-dimensional real normed space and a linear map `T` with nonzero determinant,
`∫⁻ x, g (T x) ∂μ = ‖det T‖⁻¹ * ∫⁻ y, g y ∂μ`. -/
theorem lintegral_comp_linearMap_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {T : E →ₗ[ℝ] E} (hT : LinearMap.det T ≠ 0)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g (T x) ∂μ = ENNReal.ofReal |(LinearMap.det T)⁻¹| * ∫⁻ y, g y ∂μ := by
  rw [← lintegral_map hg T.continuous_of_finiteDimensional.measurable]
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hT]
  rw [lintegral_smul_measure (ENNReal.ofReal |(LinearMap.det T)⁻¹|) g]
  rfl

/-- **The inverse form of the finite-dimensional linear change of variables.**
`∫⁻ y, g y ∂μ = ‖det T‖ * ∫⁻ x, g (T x) ∂μ` for `LinearMap.det T ≠ 0`. -/
theorem lintegral_linearMap_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {T : E →ₗ[ℝ] E} (hT : LinearMap.det T ≠ 0)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂μ = ENNReal.ofReal |LinearMap.det T| * ∫⁻ x, g (T x) ∂μ := by
  rw [lintegral_comp_linearMap_eq μ hT g hg, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg (LinearMap.det T)),
    ← abs_mul, mul_inv_cancel₀ hT, abs_one, ENNReal.ofReal_one, one_mul]

/-- The linear map `T` rescales the Haar measure by the inverse absolute determinant
(mathlib `Measure.map_linearMap_addHaar_eq_smul_addHaar`, restated). -/
theorem map_linearMap_eq_smul_addHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {T : E →ₗ[ℝ] E} (hT : LinearMap.det T ≠ 0) :
    Measure.map T μ = ENNReal.ofReal |(LinearMap.det T)⁻¹| • μ :=
  Measure.map_linearMap_addHaar_eq_smul_addHaar μ hT

/-- The preimage of a set under a linear map with nonzero determinant has measure equal to the
measure of the set times the inverse absolute determinant. -/
theorem addHaar_preimage_linearMap' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {T : E →ₗ[ℝ] E} (hT : LinearMap.det T ≠ 0) (s : Set E) :
    μ (T ⁻¹' s) = ENNReal.ofReal |(LinearMap.det T)⁻¹| * μ s :=
  Measure.addHaar_preimage_linearMap μ hT s

/-- The image of a set under a linear map has measure equal to the measure of the set times the
absolute determinant. -/
theorem addHaar_image_linearMap' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (T : E →ₗ[ℝ] E) (s : Set E) :
    μ (T '' s) = ENNReal.ofReal |LinearMap.det T| * μ s :=
  Measure.addHaar_image_linearMap μ T s

end Poincare.D7.Volume
