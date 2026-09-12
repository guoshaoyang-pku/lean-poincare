/-
Task `D12-spectral-sobolev`: per-declaration axiom audit.

Every declaration authored for D12 is printed with `#print axioms`. The expected
output is either "does not depend on any axioms" or the standard Lean/mathlib
triple `[propext, Classical.choice, Quot.sound]`; in particular no proof
placeholder may appear. The fail-closed programmatic scan (tools/d12_axiom_audit.sh)
parses this module's output.
-/
import Poincare.D12.SpectralSobolev.All

namespace Poincare.D12.SpectralSobolev

/-! ## `Basic` -/

#print axioms heatWeight
#print axioms heatWeight_zero
#print axioms heatWeight_pos
#print axioms heatWeight_nonneg
#print axioms heatWeight_le_one
#print axioms heatWeight_abs_le_one
#print axioms heatWeight_tendsto_one
#print axioms heatCoeffs
#print axioms heatCoeffs_apply
#print axioms summable_sq_heatCoeff
#print axioms heatCoeffsL2
#print axioms heatEvolve
#print axioms heatSeries_hasSum
#print axioms fourierCoeff_heatEvolve

/-! ## `HeatConvergence` -/

#print axioms heatEvolve_norm_le
#print axioms heatEvolve_tendsto_self
#print axioms heatEvolve_fourierLp
#print axioms norm_heatEvolve_fourierLp
#print axioms sq_eigenvalue_pos
#print axioms heatWeight_lt_one_of_pos

/-! ## `Poincare` -/

#print axioms fourierCoeffOn_deriv_periodic
#print axioms sq_norm_eigenvalue
#print axioms sq_norm_fourierCoeffOn_deriv_periodic
#print axioms fourierCoeffOn_zero_eq_mean
#print axioms poincare_wirtinger

/-! ## `Semigroup` -/

#print axioms heatEvolve_zero
#print axioms heatEvolve_add

/-! ## `Examples` -/

#print axioms norm_sin_le_one
#print axioms norm_cos_le_one
#print axioms sine_wave_hypotheses
#print axioms integral_sin_sq_period
#print axioms integral_cos_sq_period
#print axioms poincare_wirtinger_sine
#print axioms poincare_wirtinger_sine_saturates
#print axioms poincare_constant_sharp
#print axioms heat_evolution_first_mode_nontrivial

end Poincare.D12.SpectralSobolev
