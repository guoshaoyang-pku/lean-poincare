/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.Basic

/-!
# Regularity and measurability of the Riemannian density

For a `ChartMetric G` (smooth coefficients, positive definite everywhere) we prove:

* every metric coefficient, the determinant `x ↦ (G.matrix x).det`, the adjugate entries, and
  the inverse-metric entries `x ↦ (G.invMatrix x) i j` are smooth (`ContDiff ℝ ⊤`);
* in particular the **Riemannian density** `x ↦ G.density x = √(det g(x))` is smooth, hence
  continuous and measurable (and so is its `ℝ≥0` truncation used in `riemannianMeasure`);
* the translation between the Riemannian measure `dvol = ρ dx` and the Lebesgue measure:
  `∫ f ∂G.riemannianMeasure = ∫ f · ρ ∂volume`.

The inverse-metric smoothness is the analytic heart: mathlib has no smoothness lemma for matrix
inversion at the pinned revision, so we prove it entrywise through
`Matrix.inv_def : A⁻¹ = A.det⁻¹ʳ • A.adjugate` and the fact that the adjugate entries are
determinants (hence polynomials in the coefficients), divided by the positive determinant.
-/

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D12.VolumeIBP

/-- Propositional `if` preserves `ContDiff`: for a fixed proposition, the `if` selects one of two
smooth branches globally, so smoothness transfers. -/
lemma contDiff_if_const {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {p : Prop}
    [Decidable p] {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x => if p then f x else g x) := by
  by_cases hp : p <;> simp [hp, hf, hg]

namespace ChartMetric

variable {d : ℕ} (G : ChartMetric d)

/-- Every metric coefficient is smooth. -/
lemma entry_contDiff (i j : Fin d) : ContDiff ℝ ⊤ (fun x : Vec d => G.g x i j) :=
  G.smooth i j

/-- The metric as a function into the product space is continuous. -/
lemma g_continuous : Continuous G.g :=
  continuous_pi fun i => continuous_pi fun j => (G.smooth i j).continuous

/-- The metric matrix is continuous. -/
lemma matrix_continuous : Continuous (fun x : Vec d => G.matrix x) := by
  change Continuous G.g
  exact G.g_continuous

/-- The determinant of the metric matrix is continuous. -/
lemma det_continuous : Continuous (fun x : Vec d => (G.matrix x).det) :=
  G.matrix_continuous.matrix_det

/-- The determinant of the metric matrix is smooth (`det` is a polynomial in the entries). -/
lemma det_contDiff : ContDiff ℝ ⊤ (fun x : Vec d => (G.matrix x).det) := by
  rw [show (fun x : Vec d => (G.matrix x).det) = fun x =>
      ∑ σ : Equiv.Perm (Fin d), (σ.sign : ℝ) * ∏ k, G.g x (σ k) k by
    funext x
    rw [Matrix.det_apply']
    simp [matrix, Matrix.of_apply]]
  refine ContDiff.sum fun σ _ => ?_
  refine (contDiff_const (𝕜 := ℝ) (E := Vec d) (F := ℝ) (n := ⊤) (c := (σ.sign : ℝ))).mul ?_
  refine contDiff_prod fun k _ => ?_
  exact G.smooth (σ k) k

/-- The adjugate entries are smooth (`adjugate A i j` is the determinant of a matrix whose entries
are coefficients of `g` or constants). -/
lemma adjugate_entry_contDiff (i j : Fin d) :
    ContDiff ℝ ⊤ (fun x : Vec d => (G.matrix x).adjugate i j) := by
  rw [show (fun x : Vec d => (G.matrix x).adjugate i j) = fun x =>
      ∑ σ : Equiv.Perm (Fin d), (σ.sign : ℝ) * ∏ k,
        (if σ k = j then (Pi.single i 1 : Vec d) k else G.g x (σ k) k) by
    funext x
    rw [Matrix.adjugate_apply]
    simp [Matrix.det_apply', Matrix.updateRow_apply, matrix, Matrix.of_apply]]
  refine ContDiff.sum fun σ _ => ?_
  refine (contDiff_const (𝕜 := ℝ) (E := Vec d) (F := ℝ) (n := ⊤) (c := (σ.sign : ℝ))).mul ?_
  refine contDiff_prod fun k _ => ?_
  refine contDiff_if_const ?_ (G.smooth (σ k) k)
  exact contDiff_const (𝕜 := ℝ) (E := Vec d) (F := ℝ) (n := ⊤) (c := (Pi.single i 1 : Vec d) k)

/-- The inverse-metric entries are smooth, entrywise through the adjugate/det formula. -/
lemma invMatrix_entry_contDiff (i j : Fin d) :
    ContDiff ℝ ⊤ (fun x : Vec d => (G.invMatrix x) i j) := by
  have hfun : (fun x : Vec d => (G.invMatrix x) i j) =
      fun x => (G.matrix x).adjugate i j / (G.matrix x).det := by
    funext x
    rw [invMatrix, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, div_eq_mul_inv,
      smul_eq_mul, mul_comm]
  rw [hfun]
  exact (G.adjugate_entry_contDiff i j).div G.det_contDiff (fun x => G.det_ne_zero x)

/-- The density `√(det g)` is smooth (positive determinant keeps us away from the sqrt
singularity at `0`). -/
lemma density_contDiff : ContDiff ℝ ⊤ (fun x : Vec d => G.density x) := by
  unfold density
  change ContDiff ℝ ⊤ (Real.sqrt ∘ fun x : Vec d => (G.matrix x).det)
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  exact ContDiffAt.comp x (Real.contDiffAt_sqrt (G.det_ne_zero x)) (G.det_contDiff.contDiffAt)

/-- The density is `C¹` (in fact smooth). -/
lemma density_contDiff_one : ContDiff ℝ 1 (fun x : Vec d => G.density x) :=
  G.density_contDiff.of_le le_top

/-- The density is continuous. -/
lemma density_continuous : Continuous (fun x : Vec d => G.density x) :=
  G.density_contDiff.continuous

/-- The density is measurable. -/
lemma density_measurable : Measurable (fun x : Vec d => G.density x) :=
  G.density_continuous.measurable

/-- The density is a.e.-measurable. -/
lemma density_aemeasurable : AEMeasurable (fun x : Vec d => G.density x) :=
  G.density_measurable.aemeasurable

/-- The `ℝ≥0` density used in `riemannianMeasure` is measurable. -/
lemma densityNNReal_measurable : Measurable (fun x : Vec d => G.densityNNReal x) :=
  measurable_real_toNNReal.comp G.density_measurable

/-- The `ℝ≥0` density used in `riemannianMeasure` is a.e.-measurable. -/
lemma densityNNReal_aemeasurable : AEMeasurable (fun x : Vec d => G.densityNNReal x) :=
  G.densityNNReal_measurable.aemeasurable

/-- The `ℝ≥0` density equals the real density at every point (both sides nonnegative). -/
lemma densityNNReal_eq (x : Vec d) : (G.densityNNReal x : ℝ) = G.density x := by
  rw [densityNNReal, Real.toNNReal_of_nonneg (G.density_nonneg x), NNReal.coe_mk]

/-- Integration against the Riemannian measure is integration of `f · ρ` against Lebesgue
measure: `∫ f dvol = ∫ f · √(det g) dx`. This is the measure/geometry bridge identity. -/
lemma integral_riemannianMeasure_eq (f : Vec d → ℝ) :
    ∫ x, f x ∂G.riemannianMeasure = ∫ x, f x * G.density x := by
  rw [riemannianMeasure_def]
  rw [integral_withDensity_eq_integral_smul₀ G.densityNNReal_aemeasurable f]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [NNReal.smul_def, densityNNReal, Real.toNNReal_of_nonneg (G.density_nonneg x),
    NNReal.coe_mk, smul_eq_mul, mul_comm]

/-- Set-integral version of the bridge identity (for a measurable set). -/
lemma setIntegral_riemannianMeasure_eq (f : Vec d → ℝ) {s : Set (Vec d)} (hs : MeasurableSet s) :
    ∫ x in s, f x ∂G.riemannianMeasure = ∫ x in s, f x * G.density x := by
  rw [riemannianMeasure_def]
  rw [setIntegral_withDensity_eq_setIntegral_smul₀ G.densityNNReal_aemeasurable.restrict f hs]
  refine setIntegral_congr_ae hs ?_
  filter_upwards with x
  rw [NNReal.smul_def, densityNNReal, Real.toNNReal_of_nonneg (G.density_nonneg x),
    NNReal.coe_mk, smul_eq_mul, mul_comm]
  simp

/-- The Riemannian measure is absolutely continuous with respect to Lebesgue measure. -/
lemma riemannianMeasure_absolutelyContinuous : G.riemannianMeasure ≪ MeasureTheory.volume := by
  rw [riemannianMeasure_def]
  exact withDensity_absolutelyContinuous (μ := MeasureTheory.volume)
    (f := fun x => (G.densityNNReal x : ℝ≥0∞))

/-- The Riemannian measure of the whole space equals the `ℝ≥0∞` integral of the density
(the total volume of the chart in the metric; typically infinite on the unbounded chart). -/
lemma riemannianMeasure_univ :
    G.riemannianMeasure Set.univ = ∫⁻ x, ENNReal.ofReal (G.density x) := by
  rw [riemannianMeasure_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply lintegral_congr
  intro x
  rfl

end ChartMetric

end Poincare.D12.VolumeIBP
