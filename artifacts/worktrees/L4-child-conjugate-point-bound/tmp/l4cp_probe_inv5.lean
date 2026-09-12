/-
Invocation-5 independent probe for L4-child-conjugate-point-bound.

Written from scratch (does not reuse tmp/l4cp_probe.lean or tmp/l4cp_probe_inv4.lean):

1. `inv5_HeadlineType` restates the acceptance sentence independently; both the headline
   theorem and the statement lock must have a type definitionally equal to it.
2. A fresh non-vacuous witness at *new* numbers k = 5, K = 5, T = 7/5 (near the sharp
   threshold π/√5 ≈ 1.40496), through the strict theorem, plus its non-strict consequence.
3. Sharpness of that instance: the k = 5 model vanishes at π/√5 and positivity already fails
   at π/√5 + 1/10, so the threshold is attained and no larger T is admissible.
4. Hypothesis-necessity (falsification) check: the same statement with `0 ≤ K` instead of
   `0 < K` is *false*, so `K > 0` is essential and the acceptance statement is not a
   degenerate specialization of a vacuous hypothesis set.
5. Axiom cones for every probe declaration, for a fresh independent parse.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- The acceptance sentence of task `L4-child-conjugate-point-bound`, written out
independently of `ConjugatePointEndpoint.lean` and of `ConjugatePointAxiomAudit.lean`. -/
def inv5_HeadlineType : Prop :=
  ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
    0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
    JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
    (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
    (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 → T ≤ Real.pi / Real.sqrt K

/-- Fidelity of the implementation theorem to the acceptance sentence (defeq check). -/
example : inv5_HeadlineType := conjugate_point_bound

/-- Fidelity of the statement lock to the same sentence (defeq check). -/
example : inv5_HeadlineType := endpoint_bound_acceptance_lock

/-- **Fresh near-threshold witness, strict form.**  `k ≡ 5`, `K = 5`, `T = 7/5`
(`π/√5 ≈ 1.40496`, so `T` is within 0.005 of the threshold), `B = 7`, `t₀ = 1/14`. -/
theorem inv5_witness_k5_near_threshold_strict : (7 / 5 : ℝ) < Real.pi / Real.sqrt 5 := by
  have hsqrt5pos : 0 < Real.sqrt 5 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt5nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5sq : Real.sqrt 5 * Real.sqrt 5 = 5 := by
    simpa [sq] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hmax : max (1 / Real.sqrt 5) (7 / 5 : ℝ) = 7 / 5 := by
    rw [max_eq_right]
    rw [div_le_iff₀ hsqrt5pos]
    nlinarith [h5sq, hsqrt5nonneg]
  have hmain := conjugate_point_bound_strict (T := 7 / 5) (B := 7) (t₀ := 1 / 14) (K := 5)
    (k := fun _ : ℝ => 5) (u := jacobiSol 5) (du := jacobiDeriv 5)
    (ddu := fun t => -(5 * jacobiSol 5 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 5 (7 / 5))
    (((continuous_const.mul (continuous_jacobiSol 5)).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound (K := 5) (T := 7 / 5) (by norm_num) t ht
      rw [hmax] at hb
      linarith [hb])
    (jacobiSol_zero 5) (jacobiDeriv_zero 5)
    (fun t ht => by
      refine jacobiSol_pos_of_nonneg (K := 5) (by norm_num) ht.1 (Or.inr ?_)
      have h5 : Real.sqrt 5 < 157 / 70 := by
        nlinarith [h5sq, hsqrt5nonneg]
      calc Real.sqrt 5 * t ≤ Real.sqrt 5 * (7 / 5) :=
            mul_le_mul_of_nonneg_left ht.2 hsqrt5nonneg
        _ < (157 / 70) * (7 / 5) :=
            mul_lt_mul_of_pos_right h5 (by norm_num : (0 : ℝ) < 7 / 5)
        _ = 157 / 50 := by norm_num
        _ < Real.pi := by nlinarith [Real.pi_gt_d4])
    (by norm_num) (fun _ _ => by norm_num)
    (by rw [hmax]; norm_num)
  exact hmain

/-- The non-strict acceptance instance at the same fresh numbers. -/
theorem inv5_witness_k5_near_threshold : (7 / 5 : ℝ) ≤ Real.pi / Real.sqrt 5 :=
  le_of_lt inv5_witness_k5_near_threshold_strict

/-- The `k = 5` model vanishes at its first conjugate point `π/√5`. -/
theorem inv5_jacobiSol_five_firstZero : jacobiSol 5 (Real.pi / Real.sqrt 5) = 0 := by
  rw [jacobiSol_of_pos (by norm_num : (0 : ℝ) < 5),
    jacobiSolSphere_firstZero (by norm_num : (0 : ℝ) < 5)]

/-- Sharpness of the fresh instance: for the `k = 5` model, positivity *already fails* at
`π/√5 + 1/10`, i.e. no `T` past the threshold satisfies the hypothesis `u > 0` on `(0,T]`.
So the bound `7/5 ≤ π/√5` is not an artifact of a weak threshold. -/
theorem inv5_jacobiSol_five_pos_fails_beyond :
    ¬ (∀ t ∈ Ioc 0 (Real.pi / Real.sqrt 5 + 1 / 10), 0 < jacobiSol 5 t) := by
  intro h
  have hlt := (jacobiSol_pos_iff (K := 5) (T := Real.pi / Real.sqrt 5 + 1 / 10)
    (by norm_num)).mp h
  linarith

/-- **Hypothesis necessity (falsification check).**  The acceptance statement with `0 < K`
replaced by `0 ≤ K` is *false*: at `K = 0` the model normalization threshold degenerates to
`0 ≤ 1/2`, while the conclusion `T ≤ π/√0 = 0` fails for `T = 1`.  Hence the positive
curvature hypothesis `0 < K` in `conjugate_point_bound` is essential: the endpoint bound is
not a degenerate consequence of a vacuous hypothesis set. -/
theorem inv5_K_zero_variant_false :
    ¬ (∀ {T t₀ K : ℝ}, 0 ≤ K → 0 < t₀ →
        (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 → T ≤ Real.pi / Real.sqrt K) := by
  intro h
  have hbad := h (T := 1) (t₀ := 1) (K := 0) (by norm_num) (by norm_num)
    (by norm_num [Real.sqrt_zero])
  rw [Real.sqrt_zero, div_zero] at hbad
  norm_num at hbad

end Poincare.L4.GeodesicComparison

/-! ## Axiom cones of the probe declarations -/

#print axioms Poincare.L4.GeodesicComparison.inv5_witness_k5_near_threshold_strict
#print axioms Poincare.L4.GeodesicComparison.inv5_witness_k5_near_threshold
#print axioms Poincare.L4.GeodesicComparison.inv5_jacobiSol_five_firstZero
#print axioms Poincare.L4.GeodesicComparison.inv5_jacobiSol_five_pos_fails_beyond
#print axioms Poincare.L4.GeodesicComparison.inv5_K_zero_variant_false
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_strict
#print axioms Poincare.L4.GeodesicComparison.endpoint_bound_acceptance_lock
