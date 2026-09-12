/-
Invocation-7 acceptance-wording probe (part B).

Fresh consumer-side elaboration of the exact deliverable sentence
"non-vacuous witness (k = 2, K = 1 giving T <= pi/sqrt 1 = pi, sharpened by
pi/sqrt 2 for the k=2 solution)" plus the sharpness claims, against the frozen oleans.
Not part of the release package.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointEndpoint

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Witness instance `k = 2`, `K = 1`, `T = 2`: `2 ≤ π/√1 = π`. -/
theorem inv7b_witness_k2_K1 : (2 : ℝ) ≤ Real.pi / Real.sqrt 1 :=
  conjugate_point_bound_witness_k2_K1

/-- Sharpened witness instance `k = 2`, `K = 2`, `T = 2`: `2 ≤ π/√2`. -/
theorem inv7b_witness_k2_K2 : (2 : ℝ) ≤ Real.pi / Real.sqrt 2 :=
  conjugate_point_bound_witness_k2_K2

/-- The sharpening is strict: `π/√2 < π`, so the `K = 2` bound is strictly stronger. -/
theorem inv7b_sharpening_strict : Real.pi / Real.sqrt 2 < Real.pi :=
  pi_div_sqrt_two_lt_pi

/-- Sharpness for the `k = 2` model: positivity on `(0,T]` iff `T < π/√2`. -/
theorem inv7b_k2_threshold (T : ℝ) :
    (∀ t ∈ Ioc 0 T, 0 < jacobiSol 2 t) ↔ T < Real.pi / Real.sqrt 2 :=
  jacobiSol_two_pos_iff T

/-- Attainment: the `k = 2` model vanishes exactly at `π/√2`. -/
theorem inv7b_k2_first_zero : jacobiSol 2 (Real.pi / Real.sqrt 2) = 0 :=
  jacobiSol_two_firstZero

/-- The endpoint `T = π/√2` is inadmissible for the positivity hypothesis. -/
theorem inv7b_k2_not_pos_at_endpoint : ¬ (0 < jacobiSol 2 (Real.pi / Real.sqrt 2)) :=
  jacobiSol_two_not_pos_at_firstZero

/-- Strict endpoint form for the `k = 2`, `K = 1` instance (`T < π = π/√1`), combining the
sharpened `K = 2` witness with `π/√2 < π`. -/
theorem inv7b_witness_k2_K1_strict : (2 : ℝ) < Real.pi / Real.sqrt 1 := by
  have h := inv7b_witness_k2_K2
  have h2 : Real.pi / Real.sqrt 2 < Real.pi / Real.sqrt 1 := by
    simpa [Real.sqrt_one] using inv7b_sharpening_strict
  exact lt_of_le_of_lt h h2

end Poincare.L4.GeodesicComparison

#print axioms Poincare.L4.GeodesicComparison.inv7b_witness_k2_K1
#print axioms Poincare.L4.GeodesicComparison.inv7b_witness_k2_K2
#print axioms Poincare.L4.GeodesicComparison.inv7b_sharpening_strict
#print axioms Poincare.L4.GeodesicComparison.inv7b_k2_threshold
#print axioms Poincare.L4.GeodesicComparison.inv7b_k2_first_zero
#print axioms Poincare.L4.GeodesicComparison.inv7b_k2_not_pos_at_endpoint
#print axioms Poincare.L4.GeodesicComparison.inv7b_witness_k2_K1_strict
