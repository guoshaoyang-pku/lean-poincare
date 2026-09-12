/-
D12-spectral-sobolev: concrete witnesses for the spectral Sobolev theorems.

This file proves that the hypotheses of `poincare_wirtinger` are inhabited by a
concrete, nondegenerate function — the sine wave on the circle of length `2π` —
and records the two downstream consequences:

* the Poincaré inequality applied to the sine wave;
* equality in the inequality for the sine wave (both sides equal π), which shows
  that the constant `((b−a)/2π)²` is **optimal** — any constant valid for all
  admissible functions must be at least `1` on the length-`2π` circle;
* a concrete non-vacuity check for the heat evolution: the first Fourier mode
  decays strictly for positive time.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Poincare.D12.SpectralSobolev.Poincare
import Poincare.D12.SpectralSobolev.HeatConvergence

open scoped ENNReal ComplexConjugate Real NNReal lp Topology Interval
open MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Complex AddCircle Set

namespace Poincare.D12.SpectralSobolev

noncomputable section

/-! ## Pointwise bounds for the sine and cosine waves -/

lemma norm_sin_le_one (x : ℝ) : ‖(Real.sin x : ℂ)‖ ≤ 1 := by
  calc
    ‖(Real.sin x : ℂ)‖ = Real.sqrt (‖(Real.sin x : ℂ)‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt ((Real.sin x) ^ 2) := by
      congr 1
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      rw [sq]
    _ = |Real.sin x| := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ 1 := Real.abs_sin_le_one x

lemma norm_cos_le_one (x : ℝ) : ‖(Real.cos x : ℂ)‖ ≤ 1 := by
  calc
    ‖(Real.cos x : ℂ)‖ = Real.sqrt (‖(Real.cos x : ℂ)‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt ((Real.cos x) ^ 2) := by
      congr 1
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      rw [sq]
    _ = |Real.cos x| := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ 1 := Real.abs_cos_le_one x

/-! ## The sine wave satisfies the hypotheses -/

/-- The sine wave `x ↦ sin x` on the circle of length `2π` satisfies all the
hypotheses of `poincare_wirtinger`: continuously differentiable, matching endpoint
values, mean zero, interval-integrable derivative, and L² membership of both. -/
theorem sine_wave_hypotheses :
    (∀ x, x ∈ [[(0 : ℝ), 2 * π]] → HasDerivAt (fun x : ℝ => (Real.sin x : ℂ)) ((Real.cos x : ℂ)) x) ∧
    (Real.sin (2 * π) : ℂ) = (Real.sin 0 : ℂ) ∧
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) (fun x : ℝ => (Real.sin x : ℂ)) 0 = 0 ∧
    IntervalIntegrable (fun x : ℝ => (Real.cos x : ℂ)) volume 0 (2 * π) ∧
    MemLp (fun x : ℝ => (Real.sin x : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) ∧
    MemLp (fun x : ℝ => (Real.cos x : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Real.volume_Ioc]
      exact ne_top_of_lt ENNReal.ofReal_lt_top)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact HasDerivAt.ofReal_comp (Real.hasDerivAt_sin x)
  · norm_num [Real.sin_two_pi, Real.sin_zero]
  · rw [fourierCoeffOn_zero_eq_mean (by positivity : (0 : ℝ) < 2 * π)]
    rw [intervalIntegral.integral_ofReal]
    norm_num [integral_sin, Real.cos_two_pi, Real.cos_zero]
  · exact (continuous_ofReal.comp Real.continuous_cos).intervalIntegrable 0 (2 * π)
  · exact MemLp.of_bound
      (continuous_ofReal.comp Real.continuous_sin).aestronglyMeasurable 1
      (Eventually.of_forall fun x => norm_sin_le_one x)
  · exact MemLp.of_bound
      (continuous_ofReal.comp Real.continuous_cos).aestronglyMeasurable 1
      (Eventually.of_forall fun x => norm_cos_le_one x)

/-! ## Integrals of the sine and cosine squares over one period -/

/-- ∫₀^{2π} sin² = π. -/
theorem integral_sin_sq_period : ∫ x in (0 : ℝ)..(2 * π), ‖(Real.sin x : ℂ)‖ ^ 2 = π := by
  conv_lhs =>
    enter [1, x]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, ← sq]
  norm_num [integral_sin_sq, Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi]

/-- ∫₀^{2π} cos² = π. -/
theorem integral_cos_sq_period : ∫ x in (0 : ℝ)..(2 * π), ‖(Real.cos x : ℂ)‖ ^ 2 = π := by
  conv_lhs =>
    enter [1, x]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, ← sq]
  norm_num [integral_cos_sq, Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi]

/-! ## Downstream use of the Poincaré inequality -/

/-- Downstream use: applying `poincare_wirtinger` to the sine wave on the circle of
length `2π` gives the classical bound `∫₀^{2π} sin² ≤ ∫₀^{2π} cos²` (the constant
`((2π)/2π)²` is `1`). -/
theorem poincare_wirtinger_sine :
    ∫ x in (0 : ℝ)..(2 * π), ‖(Real.sin x : ℂ)‖ ^ 2 ≤
      ∫ x in (0 : ℝ)..(2 * π), ‖(Real.cos x : ℂ)‖ ^ 2 := by
  have h := poincare_wirtinger (a := (0 : ℝ)) (b := 2 * π) (by positivity : (0 : ℝ) < 2 * π)
    (f := fun x : ℝ => (Real.sin x : ℂ)) (f' := fun x : ℝ => (Real.cos x : ℂ))
    sine_wave_hypotheses.1 sine_wave_hypotheses.2.1 sine_wave_hypotheses.2.2.1
    sine_wave_hypotheses.2.2.2.1 sine_wave_hypotheses.2.2.2.2.1 sine_wave_hypotheses.2.2.2.2.2
  have hconst : ((2 * π - 0) / (2 * π)) ^ 2 = (1 : ℝ) := by
    field_simp [Real.pi_pos.ne']
    ring
  rw [hconst] at h
  simpa using h

/-- **Equality case (optimality witness).** The sine wave saturates the Poincaré
inequality on the circle of length `2π`: both sides equal π. Hence the constant
`((b−a)/2π)²` (equal to 1 here) cannot be improved, and the inequality is not
vacuous: both sides are π ≠ 0. -/
theorem poincare_wirtinger_sine_saturates :
    ∫ x in (0 : ℝ)..(2 * π), ‖(Real.sin x : ℂ)‖ ^ 2 =
      ((2 * π - 0) / (2 * π)) ^ 2 * ∫ x in (0 : ℝ)..(2 * π), ‖(Real.cos x : ℂ)‖ ^ 2 := by
  rw [integral_sin_sq_period, integral_cos_sq_period]
  field_simp [Real.pi_pos.ne']
  ring

/-- **Optimality of the Poincaré constant.** Any constant `C` that makes the
Poincaré inequality valid for every admissible function on the circle of length
`2π` must satisfy `((2π)/2π)² = 1 ≤ C`: the sine wave attains equality with both
sides equal to π. -/
theorem poincare_constant_sharp {C : ℝ}
    (hC : ∀ (f f' : ℝ → ℂ), (∀ x, x ∈ [[(0 : ℝ), 2 * π]] → HasDerivAt f (f' x) x) →
      f (2 * π) = f 0 → fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) f 0 = 0 →
      IntervalIntegrable f' volume 0 (2 * π) →
      MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) →
      MemLp f' 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) →
      ∫ x in (0 : ℝ)..(2 * π), ‖f x‖ ^ 2 ≤ C * ∫ x in (0 : ℝ)..(2 * π), ‖f' x‖ ^ 2) :
    ((2 * π - 0) / (2 * π)) ^ 2 ≤ C := by
  have h := hC (fun x : ℝ => (Real.sin x : ℂ)) (fun x : ℝ => (Real.cos x : ℂ))
    sine_wave_hypotheses.1 sine_wave_hypotheses.2.1 sine_wave_hypotheses.2.2.1
    sine_wave_hypotheses.2.2.2.1 sine_wave_hypotheses.2.2.2.2.1 sine_wave_hypotheses.2.2.2.2.2
  rw [integral_sin_sq_period, integral_cos_sq_period] at h
  have hconst : ((2 * π - 0) / (2 * π)) ^ 2 = (1 : ℝ) := by
    field_simp [Real.pi_pos.ne']
    ring
  rw [hconst]
  nlinarith [Real.pi_pos]

/-! ## Concrete heat-evolution non-vacuity -/

/-- Concrete non-vacuity for the spectral heat evolution on the circle of length 1:
the first Fourier mode evolves by the exact weight `exp(-(2π)² t)`, which lies
strictly between 0 and 1 for positive time, so the heat evolution is a genuine
(non-identity, nontrivial) dynamics on L². -/
theorem heat_evolution_first_mode_nontrivial (t : ℝ≥0) (ht : 0 < t) :
    ‖heatEvolve (1 : ℝ) t (fourierLp 2 1)‖ = heatWeight (1 : ℝ) t 1 ∧
      heatWeight (1 : ℝ) t 1 < 1 := by
  have : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  constructor
  · exact norm_heatEvolve_fourierLp (1 : ℝ) t 1
  · exact heatWeight_lt_one_of_pos (1 : ℝ) (by norm_num) ht (by norm_num : (1 : ℤ) ≠ 0)

end

end Poincare.D12.SpectralSobolev
