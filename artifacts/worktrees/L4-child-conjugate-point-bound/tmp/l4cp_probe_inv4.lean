/-
Independent statement + non-vacuity probe for L4-child-conjugate-point-bound,
continuation invocation 4.  Written from scratch; NOT part of the build.

It is compiled with `lake env lean` against the already-built oleans, so it inspects the
*elaborated* statements.  New content relative to `tmp/l4cp_probe.lean`:
  * the headline types are independently re-ascribed (definitional-equality check);
  * a *fresh* witness with k = 3, K = 3, T = 3/2, B = 9/2, t₀ = 1/9 (not present in the
    shipped module) exercises both the endpoint and the strict theorem end to end;
  * the direct numeric inequality 3/2 ≤ π/√3 (i.e. 2.598… ≤ π) is proved independently;
  * sharpness at K = 3 (positivity fails at the threshold; the model vanishes there);
  * failure of positivity strictly beyond the K = 2 threshold;
  * kernel cones of this probe's own declarations.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. Elaborated headline types (recorded in the log) -/

#print conjugate_point_bound
#print conjugate_point_bound_strict
#print endpoint_bound_acceptance_lock
#print rauch_upper_of_jacobi_constCurv

/-! ## 2. Independent type ascription: the headline theorem has exactly the acceptance type
(the `hzero` hypothesis `K = 0 ∨ √K·T < π` of `rauch_upper_of_jacobi_constCurv` must be
absent, otherwise this `#check` fails to elaborate). -/

#check (conjugate_point_bound :
  ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
    0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
    JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
    (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
    (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 → T ≤ Real.pi / Real.sqrt K)

/-! ## 3. Fresh non-vacuity witness: k ≡ 3, K = 3, T = 3/2, B = 9/2, t₀ = 1/9

All hypotheses are discharged explicitly, including `√3·(3/2) < 3 < π` and
`B·t₀ = (9/2)·(1/9) = 1/2`; both `conjugate_point_bound` and
`conjugate_point_bound_strict` are applied to the same data. -/

theorem inv4_witness_k3_K3_both :
    (3 : ℝ) / 2 < Real.pi / Real.sqrt 3 ∧ (3 : ℝ) / 2 ≤ Real.pi / Real.sqrt 3 := by
  have hmax : max (1 / Real.sqrt 3) ((3 : ℝ) / 2) = 3 / 2 := by
    rw [max_eq_right]
    rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hpos : ∀ t ∈ Ioc (0 : ℝ) (3 / 2), 0 < jacobiSol 3 t := by
    intro t ht
    refine jacobiSol_pos_of_nonneg (K := 3) (by norm_num) ht.1 (Or.inr ?_)
    have hle : Real.sqrt 3 * t ≤ Real.sqrt 3 * ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 3)
    have hlt : Real.sqrt 3 * ((3 : ℝ) / 2) < Real.pi := by
      have h3 : Real.sqrt 3 < 2 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
        norm_num
      nlinarith [Real.pi_gt_three]
    linarith
  have hB : ∀ t ∈ Ioo (0 : ℝ) (3 / 2), |(-(3 * jacobiSol 3 t))| ≤ (9 : ℝ) / 2 := by
    intro t ht
    have hb := jacobiSol_second_deriv_bound (K := 3) (T := 3 / 2) (by norm_num) t ht
    rw [hmax] at hb
    linarith
  constructor
  · exact conjugate_point_bound_strict (T := 3 / 2) (B := 9 / 2) (t₀ := 1 / 9) (K := 3)
      (k := fun _ : ℝ => 3) (u := jacobiSol 3) (du := jacobiDeriv 3)
      (ddu := fun t => -(3 * jacobiSol 3 t))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (jacobiSol_jacobiSolutionOn 3 (3 / 2))
      (((continuous_const.mul (continuous_jacobiSol 3)).neg).continuousOn)
      hB (jacobiSol_zero 3) (jacobiDeriv_zero 3) hpos
      (by norm_num) (fun _ _ => by norm_num)
      (by rw [hmax]; norm_num)
  · exact conjugate_point_bound (T := 3 / 2) (B := 9 / 2) (t₀ := 1 / 9) (K := 3)
      (k := fun _ : ℝ => 3) (u := jacobiSol 3) (du := jacobiDeriv 3)
      (ddu := fun t => -(3 * jacobiSol 3 t))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (jacobiSol_jacobiSolutionOn 3 (3 / 2))
      (((continuous_const.mul (continuous_jacobiSol 3)).neg).continuousOn)
      hB (jacobiSol_zero 3) (jacobiDeriv_zero 3) hpos
      (by norm_num) (fun _ _ => by norm_num)
      (by rw [hmax]; norm_num)

/-! ## 4. The numeric content of the fresh witness, proved directly -/

theorem inv4_numeric_k3 : (3 : ℝ) / 2 ≤ Real.pi / Real.sqrt 3 := by
  rw [le_div_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3))]
  have h3 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  nlinarith [Real.pi_gt_three]

/-! ## 5. Sharpness at K = 3 and failure beyond the K = 2 threshold -/

theorem inv4_k3_firstZero : jacobiSol 3 (Real.pi / Real.sqrt 3) = 0 := by
  rw [jacobiSol_of_pos (by norm_num : (0 : ℝ) < 3),
    jacobiSolSphere_firstZero (by norm_num : (0 : ℝ) < 3)]

theorem inv4_k3_not_pos_at_threshold :
    ¬ (∀ t ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 3), 0 < jacobiSol 3 t) := by
  rw [jacobiSol_pos_iff (K := 3) (by norm_num)]
  exact lt_irrefl _

theorem inv4_k2_not_pos_beyond :
    ¬ (∀ t ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 2 + 1), 0 < jacobiSol 2 t) := by
  rw [jacobiSol_two_pos_iff]
  linarith

/-! ## 6. Kernel cones of this probe's own declarations -/

#print axioms inv4_witness_k3_K3_both
#print axioms inv4_numeric_k3
#print axioms inv4_k3_firstZero
#print axioms inv4_k3_not_pos_at_threshold
#print axioms inv4_k2_not_pos_beyond

end Poincare.L4.GeodesicComparison
