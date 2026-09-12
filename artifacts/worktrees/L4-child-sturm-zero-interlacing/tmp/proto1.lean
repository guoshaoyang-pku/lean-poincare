import Poincare.D12.ComparisonGeodesics.SturmComparison
import Poincare.D10.JacobiConstantCurvature.Comparison

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Prototype: D10 model is a D12 Jacobi solution. -/
theorem proto_jacobiSol_jacobiSolutionOn (K T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => K) (jacobiSol K) (jacobiDeriv K)
      (fun t => -(K * jacobiSol K t)) 0 T where
  hasDerivAt_u := by intro t _; exact hasDerivAt_jacobiSol K t
  hasDerivAt_du := by intro t _; exact hasDerivAt_jacobiDeriv K t
  eq_secondDeriv := by intro t _; ring
  continuousOn_u := (continuous_jacobiSol K).continuousOn
  continuousOn_du :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn

/-- Prototype: engine application with the D10 model. -/
theorem proto_engine {k : ℝ → ℝ} {K : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K)
    (hk : ∀ t ∈ Icc (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0) :
    (∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), u c = 0) ∨
      (∀ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), k t = K) := by
  have hz : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  exact sturm_zero_comparison hz hk h (proto_jacobiSol_jacobiSolutionOn K _)
    hu0 (jacobiSol_zero K) (jacobiSol_firstZero hK)
    (fun t ht => by
      rw [jacobiSol_of_pos hK]
      refine jacobiSolSphere_pos hK ht.1 ?_
      have := mul_lt_mul_of_pos_left ht.2 (Real.sqrt_pos_of_pos hK)
      rwa [mul_div_cancel₀ _ (Real.sqrt_pos_of_pos hK).ne'] at this)
    (hasDerivAt_jacobiSol K _)

end Poincare.L4.GeodesicComparison
