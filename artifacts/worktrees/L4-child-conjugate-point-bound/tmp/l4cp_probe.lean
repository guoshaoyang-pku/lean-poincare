/-
Independent statement probe for L4-child-conjugate-point-bound (continuation invocation).

This file is NOT part of the build.  It is compiled with `lake env lean` against the
already-built oleans, so it inspects the *elaborated* statements rather than the source
text.  It re-states the two witness inequalities and the sharp-threshold theorem as
independent `example`s and dumps the kernel axiom cones.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit

open Set

-- Elaborated statement of the headline theorem.
#print Poincare.L4.GeodesicComparison.conjugate_point_bound

-- Elaborated statement of the strict strengthening.
#print Poincare.L4.GeodesicComparison.conjugate_point_bound_strict

-- Elaborated witness `k = 2`, `K = 1`.
#print Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K1

-- Elaborated sharpened witness `k = 2`, `K = 2`.
#print Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K2

-- Exact sharp threshold for the constant-curvature model.
#print Poincare.L4.GeodesicComparison.jacobiSol_pos_iff

-- Exact sharp threshold, `K = 2` specialization.
#print Poincare.L4.GeodesicComparison.jacobiSol_two_pos_iff

-- The first zero of the `k = 2` model.
#print Poincare.L4.GeodesicComparison.jacobiSol_two_firstZero

-- Independent restatements (elaboration must succeed against the compiled olean).
example : (2 : ℝ) ≤ Real.pi / Real.sqrt 1 :=
  Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K1

example : (2 : ℝ) ≤ Real.pi / Real.sqrt 2 :=
  Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K2

example (T : ℝ) : (∀ t ∈ Ioc 0 T, 0 < Poincare.D10.jacobiSol 2 t) ↔
    T < Real.pi / Real.sqrt 2 :=
  Poincare.L4.GeodesicComparison.jacobiSol_two_pos_iff T

example : Poincare.D10.jacobiSol 2 (Real.pi / Real.sqrt 2) = 0 :=
  Poincare.L4.GeodesicComparison.jacobiSol_two_firstZero

-- Near-threshold instance (stronger than the shipped T = 2 witness): the theorem applied at
-- T = 11/5 = 2.2 < π/√2 ≈ 2.22144, with B = 22/5 and t₀ = 1/10.  This exercises the
-- normalization thresholds at a different, larger T and needs the sharper bound
-- `Real.pi_gt_d4 : 3.1415 < π` for positivity of the model on (0, 11/5].
example : (11 / 5 : ℝ) ≤ Real.pi / Real.sqrt 2 := by
  have hmax : max (1 / Real.sqrt 2) ((11 : ℝ) / 5) = (11 : ℝ) / 5 := by
    rw [max_eq_right]
    rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hpos : ∀ t ∈ Ioc (0 : ℝ) (11 / 5), 0 < Poincare.D10.jacobiSol 2 t := by
    intro t ht
    refine Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg (K := 2) (by norm_num) ht.1 (Or.inr ?_)
    have hle : Real.sqrt 2 * t ≤ Real.sqrt 2 * ((11 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 2)
    have hlt : Real.sqrt 2 * ((11 : ℝ) / 5) < Real.pi := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2,
        Real.pi_gt_d4]
    linarith
  have hB : ∀ t ∈ Ioo (0 : ℝ) (11 / 5),
      |(-(2 * Poincare.D10.jacobiSol 2 t))| ≤ (22 : ℝ) / 5 := by
    intro t ht
    have hb := Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound
      (K := 2) (T := 11 / 5) (by norm_num) t ht
    rw [hmax] at hb
    linarith
  exact Poincare.L4.GeodesicComparison.conjugate_point_bound
    (T := 11 / 5) (B := 22 / 5) (t₀ := 1 / 10) (K := 2)
    (k := fun _ : ℝ => 2) (u := Poincare.D10.jacobiSol 2)
    (du := Poincare.D10.jacobiDeriv 2)
    (ddu := fun t => -(2 * Poincare.D10.jacobiSol 2 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Poincare.L4.GeodesicComparison.jacobiSol_jacobiSolutionOn 2 (11 / 5))
    (((continuous_const.mul (Poincare.D10.continuous_jacobiSol 2)).neg).continuousOn)
    hB
    (Poincare.D10.jacobiSol_zero 2) (Poincare.D10.jacobiDeriv_zero 2)
    hpos
    (by norm_num) (fun _ _ => by norm_num)
    (by rw [hmax]; norm_num)

-- Kernel cones of the headline, witness and lock declarations.
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_strict
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K1
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K2
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_iff
#print axioms Poincare.L4.GeodesicComparison.endpoint_bound_acceptance_lock
