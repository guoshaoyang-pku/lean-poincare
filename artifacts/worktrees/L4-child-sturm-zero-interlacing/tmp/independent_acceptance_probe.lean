/-
Independent acceptance probe for `L4-child-sturm-zero-interlacing`.

This file is **not** part of the release deliverable.  It exists so that the acceptance
decision does not rest only on the module's own witnesses: every theorem below exercises a
delivered theorem on data that the deliverable never uses, and every proof is new here.

Probes:
* `probe_interlacing_k3_k1`   — the general two-curvature interlacing with (k₁,k₂) = (3,1)
  (the deliverable's own instance is (1,1/2), the prior art's is (2,1)).
* `probe_firstZero_k3_lt_sin` — the same instance in first-positive-zero form against the
  closed forms of both first zeros.
* `probe_zero_count_equality_K4` — the *equality case* `k ≡ K = 4` of the zero-counting
  corollary (the part whose proof is new relative to the prior art: Wronskian constancy gives
  the endpoint zero).
* `probe_firstZero_bound_K4`  — the first-zero bound at K = 4.
* `probe_horizon_K1`          — the horizon form of the zero-counting corollary.
* `probe_mul_cos_le_sin_at_three_pi_div_four` — the Wronskian inequality off the endpoints.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck

noncomputable section

open Set

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Probe A: the higher-curvature model `jacobiSol 3` has a zero strictly inside `(0,π)`,
the interval between the consecutive zeros `0` and `π` of `sin` (curvature `1`). -/
theorem probe_interlacing_k3_k1 : ∃ c ∈ Ioo (0 : ℝ) Real.pi, jacobiSol 3 c = 0 := by
  have hstrict : ∃ t ∈ Ioo (0 : ℝ) Real.pi, (1 : ℝ) < 3 :=
    ⟨Real.pi / 2, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, by norm_num⟩
  exact exists_zero_of_curvature_lt (a := 0) (b := Real.pi)
    (k₁ := fun _ : ℝ => 3) (k₂ := fun _ : ℝ => 1)
    (u₁ := jacobiSol 3) (du₁ := jacobiDeriv 3) (ddu₁ := fun t => -(3 * jacobiSol 3 t))
    (u₂ := Real.sin) (du₂ := Real.cos) (ddu₂ := fun t => -Real.sin t)
    Real.pi_pos (fun t _ => by norm_num)
    (modelJacobiSolutionOn 3 Real.pi) (sinJacobiSolutionOn 0 Real.pi)
    (jacobiSol_zero 3) Real.sin_zero Real.sin_pi
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
    (by simpa using Real.hasDerivAt_sin Real.pi) hstrict

/-- Probe B: the same instance in first-zero form, using both closed forms:
`firstPositiveZero (jacobiSol 3) = π/√3 < π = firstPositiveZero sin`. -/
theorem probe_firstZero_k3_lt_sin :
    firstPositiveZero (jacobiSol 3) < firstPositiveZero Real.sin := by
  have h := firstPositiveZero_lt_of_curvature_lt (b := Real.pi)
    (k₁ := fun _ : ℝ => 3) (k₂ := fun _ : ℝ => 1)
    (u₁ := jacobiSol 3) (du₁ := jacobiDeriv 3) (ddu₁ := fun t => -(3 * jacobiSol 3 t))
    (u₂ := Real.sin) (du₂ := Real.cos) (ddu₂ := fun t => -Real.sin t)
    Real.pi_pos (fun t _ => by norm_num)
    (modelJacobiSolutionOn 3 Real.pi) (sinJacobiSolutionOn 0 Real.pi)
    (jacobiSol_zero 3) Real.sin_zero Real.sin_pi
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
    (by simpa using Real.hasDerivAt_sin Real.pi)
    ⟨Real.pi / 2, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, by norm_num⟩
  simpa [firstPositiveZero_modelJacobiSol (by norm_num : (0 : ℝ) < 3), firstPositiveZero_sin]
    using h

/-- Probe C: the equality case `k ≡ K = 4` of the zero-counting corollary produces a zero in
`(0, π/√4] = (0, π/2]`; this is exactly the endpoint zero obtained by Wronskian constancy. -/
theorem probe_zero_count_equality_K4 :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 4), jacobiSol 4 c = 0 :=
  exists_jacobi_zero_on_Ioc_pi_sqrt (K := 4) (k := fun _ : ℝ => 4)
    (u := jacobiSol 4) (du := jacobiDeriv 4) (ddu := fun t => -(4 * jacobiSol 4 t))
    (by norm_num) (fun t _ => le_rfl) (modelJacobiSolutionOn 4 (Real.pi / Real.sqrt 4))
    (jacobiSol_zero 4)

/-- Probe D: the first-positive-zero bound at `K = 4`. -/
theorem probe_firstZero_bound_K4 :
    firstPositiveZero (jacobiSol 4) ≤ Real.pi / Real.sqrt 4 :=
  firstPositiveZero_le_pi_sqrt (K := 4) (k := fun _ : ℝ => 4)
    (u := jacobiSol 4) (du := jacobiDeriv 4) (ddu := fun t => -(4 * jacobiSol 4 t))
    (by norm_num) (fun t _ => le_rfl) (modelJacobiSolutionOn 4 (Real.pi / Real.sqrt 4))
    (jacobiSol_zero 4)

/-- Probe E: the horizon form of the zero-counting corollary with horizon `H = 4`. -/
theorem probe_horizon_K1 :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 1), jacobiSol 1 c = 0 := by
  refine exists_jacobi_zero_of_horizon (K := 1) (H := 4) (k := fun _ : ℝ => 1)
    (u := jacobiSol 1) (du := jacobiDeriv 1) (ddu := fun t => -(1 * jacobiSol 1 t))
    (by norm_num) (fun t _ => le_rfl) (modelJacobiSolutionOn 1 4) (jacobiSol_zero 1)
    (jacobiDeriv_zero 1) ?_
  rw [Real.sqrt_one, div_one]
  linarith [Real.pi_lt_four]

/-- Probe F: the Wronskian inequality at an interior evaluation point. -/
theorem probe_mul_cos_le_sin_at_three_pi_div_four :
    (3 * Real.pi / 4) * Real.cos (3 * Real.pi / 4) ≤ Real.sin (3 * Real.pi / 4) :=
  mul_cos_le_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-! ### Signature fidelity of the acceptance-critical statements -/

#check @Poincare.L4.GeodesicComparison.firstPositiveZero_le_pi_sqrt_of_horizon
#check @Poincare.L4.GeodesicComparison.firstPositiveZero_mem_of_normalized
#check @Poincare.L4.GeodesicComparison.firstPositiveZero_lt_of_curvature_lt
#check @Poincare.L4.GeodesicComparison.wronskian_sin_linear_antitoneOn
#check @Poincare.L4.GeodesicComparison.wronskian_deriv_sin_linear

/-! ### Axiom cones of the probe theorems (must stay in the allowed cone) -/

#print axioms Poincare.L4.GeodesicComparison.probe_interlacing_k3_k1
#print axioms Poincare.L4.GeodesicComparison.probe_firstZero_k3_lt_sin
#print axioms Poincare.L4.GeodesicComparison.probe_zero_count_equality_K4
#print axioms Poincare.L4.GeodesicComparison.probe_firstZero_bound_K4
#print axioms Poincare.L4.GeodesicComparison.probe_horizon_K1
#print axioms Poincare.L4.GeodesicComparison.probe_mul_cos_le_sin_at_three_pi_div_four

end Poincare.L4.GeodesicComparison
