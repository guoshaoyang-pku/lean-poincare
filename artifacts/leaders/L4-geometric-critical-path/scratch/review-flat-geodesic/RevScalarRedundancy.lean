/-
Adversarial-review scratch file #4 (reviewer-owned, NOT part of the release tree).

Redundancy probe: M3's `scalarRadialJacobiSolutionOn` claims to give the U3 scalar layer a
"fully proved flat-model inhabitant".  This file shows that the *same* inhabitant is already
available in the tree from the pre-existing constant-curvature model
(`ConstantCurvatureRauch.jacobiSol_jacobiSolutionOn` at `K = 0`, whose flat branch
`jacobiSolFlat t = t` is definitional), with **no import of M3**.
-/
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch

open Set

namespace RevScalarRedundancy

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- M3's scalar statement, re-derived from the pre-existing D10 constant-curvature model
at `K = 0`. -/
theorem rev_scalar_via_constCurv (T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => 0) (fun t : ℝ => t) (fun _ : ℝ => 1)
      (fun _ : ℝ => 0) 0 T := by
  have h := Poincare.L4.GeodesicComparison.jacobiSol_jacobiSolutionOn (0 : ℝ) T
  have hfun : jacobiSol (0 : ℝ) = fun t : ℝ => t := by
    funext t
    rw [jacobiSol_of_zero]
    rfl
  have hder : jacobiDeriv (0 : ℝ) = fun _ : ℝ => (1 : ℝ) := by
    funext t
    rw [jacobiDeriv_of_zero]
  simpa only [hfun, hder, zero_mul, neg_zero] using h

end RevScalarRedundancy
