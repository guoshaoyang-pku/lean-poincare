import Poincare.L4.Compactness.RicciToDoublingHyperbolic

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Poincare.L4.Compactness
open Poincare.D12.ComparisonGeodesics

example (d : ℕ) (x : ℝ) :
    HasDerivAtR (fun y : ℝ => (Real.sinh y) ^ (d + 1) * Real.cosh y)
      ((((d + 1 : ℕ) : ℝ) * Real.sinh x ^ d * Real.cosh x) * Real.cosh x
        + Real.sinh x ^ (d + 1) * Real.sinh x) x := by
  have hpow : HasDerivAtR (fun y : ℝ => Real.sinh y ^ (d + 1))
      (((d + 1 : ℕ) : ℝ) * Real.sinh x ^ ((d + 1) - 1) * Real.cosh x) x := by
    simpa using (Real.hasDerivAt_sinh x).pow (d + 1)
  have hcosh : HasDerivAtR (fun y : ℝ => Real.cosh y) (Real.sinh x) x :=
    Real.hasDerivAt_cosh x
  have hmul := hpow.mul hcosh
  simpa [Pi.mul_apply, Nat.add_sub_cancel] using hmul

example (d : ℕ) (s : ℝ) :
    (∫ t in (0)..s, Real.sinh t ^ d) = ∫ t in (0)..s, Real.sinh t ^ d := rfl

end Poincare.L4.Compactness
