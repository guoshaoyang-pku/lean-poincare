/-
D12-spectral-sobolev: the heat evolution is a genuine semigroup.

The spectral heat operators defined in `Basic.lean` satisfy

* `H₀ f = f` (the series with all weights 1 reproduces f), and
* `H_s (H_t f) = H_{s+t} f` (composition law, from `exp(-λs)·exp(-λt) = exp(-λ(s+t))`),

making `t ↦ H_t` a one-parameter semigroup of contractions on L² of the 1-torus.
-/
import Poincare.D12.SpectralSobolev.Basic

open scoped ENNReal ComplexConjugate Real NNReal lp Topology
open MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Complex AddCircle

namespace Poincare.D12.SpectralSobolev

noncomputable section

/-- At time 0 the heat evolution is the identity: all weights `exp(0) = 1`. -/
theorem heatEvolve_zero (T : ℝ) [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) :
    heatEvolve T 0 f = f := by
  apply (fourierBasis (T := T)).repr.injective
  ext n
  rw [fourierBasis_repr, fourierCoeff_heatEvolve, heatCoeffs_apply, heatWeight_zero]
  norm_num
  simpa using (fourierBasis_repr (T := T) f n).symm

/-- **Semigroup law**: `H_s (H_t f) = H_{s+t} f` for all nonnegative `s, t`. -/
theorem heatEvolve_add (T : ℝ) [hT : Fact (0 < T)] (s t : ℝ≥0)
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) :
    heatEvolve T s (heatEvolve T t f) = heatEvolve T (s + t) f := by
  apply (fourierBasis (T := T)).repr.injective
  ext n
  rw [fourierBasis_repr, fourierCoeff_heatEvolve, heatCoeffs_apply]
  rw [fourierBasis_repr, fourierCoeff_heatEvolve, heatCoeffs_apply,
    fourierCoeff_heatEvolve, heatCoeffs_apply]
  have hw : heatWeight T s n * heatWeight T t n = heatWeight T (s + t) n := by
    unfold heatWeight
    rw [← Real.exp_add]
    congr 1
    rw [NNReal.coe_add]
    ring
  rw [← mul_assoc]
  rw [show (heatWeight T s n : ℂ) * heatWeight T t n = heatWeight T (s + t) n by
    exact_mod_cast hw]

end

end Poincare.D12.SpectralSobolev
