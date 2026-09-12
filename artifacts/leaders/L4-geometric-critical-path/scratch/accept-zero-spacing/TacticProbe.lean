import Poincare.L4.GeodesicComparison.ZeroSpacing

open Poincare.D12.ComparisonGeodesics

-- can fun_prop prove HasDerivAt goals?
example (t : ℝ) : HasDerivAtR (fun s : ℝ => Real.sin (2 * s)) (2 * Real.cos (2 * t)) t := by
  fun_prop

example (t : ℝ) : HasDerivAtR (fun s : ℝ => (Real.cos (2 * s)) ^ 2) (-4 * Real.sin (2 * t) * Real.cos (2 * t)) t := by
  fun_prop

example (t : ℝ) : deriv (fun s : ℝ => (Real.sin (2 * s)) * (1 + (1 / 10) * Real.cos (2 * s))) t
    = 2 * Real.cos (2 * t) + (1 / 5) * (Real.cos (2 * t)) ^ 2 - (1 / 5) * (Real.sin (2 * t)) ^ 2 := by
  simp only [deriv_mul, deriv_add, deriv_const_mul, deriv_const, deriv_one, deriv_cos, deriv_sin,
    deriv_id'', mul_one, zero_mul, add_zero, mul_zero, zero_add, Pi.mul_apply]
  ring
