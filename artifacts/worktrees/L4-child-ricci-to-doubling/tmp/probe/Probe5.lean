import Poincare.L4.Compactness.RicciToDoublingHyperbolic

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Poincare.L4.Compactness
open Poincare.D12.ComparisonGeodesics

example (x : ℝ) : HasDerivAtR (fun y : ℝ => Real.cosh y) (Real.sinh x) x :=
  Real.hasDerivAt_cosh x

example (d : ℕ) (x : ℝ) : HasDerivAtR (fun y : ℝ => Real.sinh y ^ (d + 1))
    (((d + 1 : ℕ) : ℝ) * Real.sinh x ^ ((d + 1) - 1) * Real.cosh x) x :=
  (Real.hasDerivAt_sinh x).pow (d + 1)

example (d : ℕ) (x : ℝ) : HasDerivAtR (fun y : ℝ => (Real.sinh y) ^ (d + 1) * Real.cosh y)
    ((((d + 1 : ℕ) : ℝ) * Real.sinh x ^ d * Real.cosh x) * Real.cosh x
      + Real.sinh x ^ (d + 1) * Real.sinh x) x := by
  have hpow : HasDerivAtR (fun y : ℝ => Real.sinh y ^ (d + 1))
      (((d + 1 : ℕ) : ℝ) * Real.sinh x ^ d * Real.cosh x) x := by
    convert (Real.hasDerivAt_sinh x).pow (d + 1) using 1
    · ext y; rfl
    · rw [Nat.add_sub_cancel]
  have hcosh : HasDerivAtR (fun y : ℝ => Real.cosh y) (Real.sinh x) x :=
    Real.hasDerivAt_cosh x
  have hmul := hpow.mul hcosh
  convert hmul using 1
  · ext y; rfl
  · ring

end Poincare.L4.Compactness
