import Poincare.L4.Compactness.RicciToDoublingHyperbolic

noncomputable section
open Set MeasureTheory
open scoped Topology

example (x : ℝ) : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x

example (x : ℝ) : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := by
  simpa using (hasDerivAt_id x : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x)

example (d : ℕ) (κ x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.sinh (κ * y)) ^ d) ((d : ℝ) * (Real.sinh (κ * x)) ^ (d - 1) * (Real.cosh (κ * x) * κ)) x := by
  have hinner : HasDerivAt (fun y : ℝ => κ * y) κ x := by
    simpa using (hasDerivAt_id x).const_mul κ
  have hsin : HasDerivAt (fun y : ℝ => Real.sinh y) (Real.cosh (κ * x)) (κ * x) :=
    Real.hasDerivAt_sinh (κ * x)
  have hpow : HasDerivAt (fun y : ℝ => Real.sinh y ^ d)
      ((d : ℝ) * Real.sinh (κ * x) ^ (d - 1) * Real.cosh (κ * x)) (κ * x) := hsin.pow d
  have hcomp := HasDerivAt.comp (x := x) (h := fun y : ℝ => κ * y)
    (h₂ := fun y : ℝ => Real.sinh y ^ d) hpow hinner
  convert hcomp using 1
  · ext y; simp [Function.comp]
  · ring

end
