import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

namespace Review5

open Poincare.D12.VolumeIBP Poincare.D13.ManifoldIBP

/-- A concrete bump on `Vec 1 = ℝ¹` supported in `closedBall 0 (3/4) ⊂ {y | y 0 < 1}`. -/
noncomputable def b : ContDiffBump (0 : Vec 1) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

theorem bump_hypotheses :
    ContDiff ℝ 2 (fun _ : Vec 1 => (0 : ℝ)) ∧ ContDiff ℝ 2 (b : Vec 1 → ℝ) ∧
      HasCompactSupport (b : Vec 1 → ℝ) ∧
      tsupport (b : Vec 1 → ℝ) ⊆ {y : Vec 1 | y 0 < 1} := by
  refine ⟨contDiff_const, b.contDiff, b.hasCompactSupport, ?_⟩
  rw [ContDiffBump.tsupport_eq]
  intro y hy
  have hb : b.rOut = 3 / 4 := rfl
  rw [hb] at hy
  have h1 : ‖y‖ ≤ (3 / 4 : ℝ) := by simpa [dist_eq_norm] using hy
  have h2 : |y 0| ≤ ‖y‖ := by simpa using norm_le_pi_norm (f := y) 0
  have h3 : y 0 ≤ 3 / 4 := le_trans (le_abs_self _) (le_trans h2 h1)
  have h4 : (3 : ℝ) / 4 < 1 := by norm_num
  exact lt_of_le_of_lt h3 h4

/-- The L4 theorem applies to the concrete data `G = ChartMetric.euclideanChartMetric 1`, `F = 0`,
`V = b`: its conclusion (integrability + nonnegativity) is a genuine, instantiated
assertion. -/
example : Integrable (fun m => (ChartMetric.euclideanChartMetric 1).gradInnerInverse
      (b : Vec 1 → ℝ) (b : Vec 1 → ℝ) m)
    (((OverlapAtlas.hsAtlas (ChartMetric.euclideanChartMetric 1)).globalMeasure volume).withDensity
      ((OverlapAtlas.hsAtlas (ChartMetric.euclideanChartMetric 1)).weight (fun _ : Vec 1 => 0))) :=
  (Poincare.L4.ManifoldIBP.halfSpaceAtlas_dirichletEnergy_nonneg (ChartMetric.euclideanChartMetric 1)
    (fun _ : Vec 1 => 0) (b : Vec 1 → ℝ) bump_hypotheses.1 bump_hypotheses.2.1
    bump_hypotheses.2.2.1 bump_hypotheses.2.2.2).1

end Review5
