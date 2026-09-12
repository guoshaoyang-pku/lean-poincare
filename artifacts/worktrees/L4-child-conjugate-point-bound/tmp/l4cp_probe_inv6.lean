/-
Invocation 6 — independent probe for `L4-child-conjugate-point-bound`.

Content (all new relative to inv2–inv5 probes):

* `Inv6HeadlineType` / `inv6_statement_fidelity` — the acceptance sentence written out
  independently (from the task text, not copied from the audit module) and *proved by
  ascription* to `conjugate_point_bound`.  Elaboration requires the two types to be
  definitionally equal, so any silent weakening of a hypothesis or of the conclusion
  breaks this probe.
* `inv6_hpos_necessary` — falsification: the variant of the acceptance sentence with the
  positivity hypothesis `u > 0` on `(0,T]` *dropped* is FALSE.  Counterexample:
  `k ≡ 2`, `K = 2`, `u = jacobiSol 2`, `T = 3 > π/√2` (where `jacobiSol 2` is already
  negative), `B = √2`, `t₀ = 1/12`.
* `inv6_hk_necessary` — falsification: the variant with the domination hypothesis
  `K ≤ k` on `(0,T)` *dropped* is FALSE.  Counterexample: `k ≡ 1`, `K = 2`,
  `u = jacobiSol 1 = sin`, `T = 3 > π/√2` (still positive since `3 < π`), `B = 1`,
  `t₀ = 1/12`.
* `inv6_near_threshold_witness[_strict]` — a new non-vacuous witness at `k ≡ K = 4`,
  `T = 314159/200000 = 1.570795`, i.e. `T/(π/√4) = 3.14159/π > 0.9999991`: the bound
  `T ≤ π/√4` is met within `9·10⁻⁷` of the sharp threshold by a genuine solution.
  (Prior probes used K = 1, 2, 3, 5.)
* `#print axioms` queries for every probe declaration.

This file is a probe, not part of the deliverable; it is compiled against the frozen
artifact oleans and is not imported by the audit module.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointEndpoint

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## A. Independent statement ascription -/

/-- The acceptance sentence of `L4-child-conjugate-point-bound`, written out independently:
`k ≥ K > 0` on `(0,T)`, `u 0 = 0`, `u' 0 = 1`, `u > 0` on `(0,T]`, and the analytic
normalization hypotheses of `rauch_upper_of_jacobi_constCurv`, imply `T ≤ π/√K`. -/
def Inv6HeadlineType : Prop :=
  ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
    0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
    JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
    (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
    (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 → T ≤ Real.pi / Real.sqrt K

/-- The deliverable's headline theorem has exactly the independently written acceptance
type: this term elaborates only if `conjugate_point_bound`'s type is definitionally equal
to `Inv6HeadlineType`. -/
theorem inv6_statement_fidelity : Inv6HeadlineType :=
  conjugate_point_bound

/-! ## B. Numeric lemmas used by the falsifications -/

/-- `π/√2 < 3` (since `π < 3.15 < 3·1.4 < 3·√2`). -/
theorem inv6_pi_div_sqrt_two_lt_three : Real.pi / Real.sqrt 2 < 3 := by
  rw [div_lt_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
  have h14 : (1.4 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  nlinarith [Real.pi_lt_d2]

/-- `√4 = 2`. -/
theorem inv6_sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- Second-derivative bound for `jacobiSol 2` on `(0,3)`: with `B = √2` all of `(0,3)`
is covered, including the region past the conjugate point `π/√2`. -/
theorem inv6_jacobiSolTwo_abs_second_deriv_le_sqrt_two :
    ∀ t ∈ Ioo (0 : ℝ) 3, |(-(2 * jacobiSol 2 t))| ≤ Real.sqrt 2 := by
  intro t _ht
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos h2pos
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by simpa [sq] using Real.sq_sqrt h2pos.le
  have hsin : |Real.sin (Real.sqrt 2 * t)| ≤ 1 := Real.abs_sin_le_one _
  rw [jacobiSol_of_pos h2pos, jacobiSolSphere]
  have hval : |(-(2 * (Real.sin (Real.sqrt 2 * t) / Real.sqrt 2)))|
      = (2 * |Real.sin (Real.sqrt 2 * t)|) / Real.sqrt 2 := by
    rw [abs_neg, abs_mul, abs_of_nonneg h2pos.le, abs_div, abs_of_nonneg hsqrt2pos.le,
      mul_div_assoc']
  rw [hval, div_le_iff₀ hsqrt2pos]
  calc 2 * |Real.sin (Real.sqrt 2 * t)| ≤ 2 * 1 :=
        mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = Real.sqrt 2 * Real.sqrt 2 := by rw [hsq]; ring

/-- Second-derivative bound for `jacobiSol 1 = sin` on `(0,3)`: `B = 1`. -/
theorem inv6_jacobiSolOne_abs_second_deriv_le_one :
    ∀ t ∈ Ioo (0 : ℝ) 3, |(-(1 * jacobiSol 1 t))| ≤ 1 := by
  intro t _ht
  rw [jacobiSol_of_pos (by norm_num : (0 : ℝ) < 1), jacobiSolSphere, Real.sqrt_one]
  have hsin : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  simpa using hsin

/-! ## C. Falsification: positivity on `(0,T]` is essential -/

/-- Dropping `u > 0` on `(0,T]` makes the acceptance sentence false: the `k ≡ 2`, `K = 2`
solution `jacobiSol 2` satisfies every remaining hypothesis on `(0,3)` with `B = √2`,
`t₀ = 1/12`, but `3 > π/√2`. -/
theorem inv6_hpos_necessary :
    ¬ (∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
        0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
        JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
        (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
        0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
        (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 → T ≤ Real.pi / Real.sqrt K) := by
  intro H
  have h := H (k := fun _ : ℝ => 2) (u := jacobiSol 2) (du := jacobiDeriv 2)
    (ddu := fun t => -(2 * jacobiSol 2 t)) (T := 3) (B := Real.sqrt 2)
    (t₀ := 1 / 12) (K := 2)
    (by norm_num)
    (Real.sqrt_nonneg 2)
    (by norm_num)
    (by norm_num)
    (by
      have h6 : Real.sqrt 2 ≤ 6 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      linarith)
    (jacobiSol_jacobiSolutionOn 2 3)
    (((continuous_const.mul (continuous_jacobiSol 2)).neg).continuousOn)
    inv6_jacobiSolTwo_abs_second_deriv_le_sqrt_two
    (jacobiSol_zero 2) (jacobiDeriv_zero 2)
    (by norm_num)
    (fun _ _ => le_rfl)
    (by
      have hmax : max (1 / Real.sqrt 2) (3 : ℝ) = 3 := by
        rw [max_eq_right]
        rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      rw [hmax]
      norm_num)
  exact absurd h (not_le.mpr inv6_pi_div_sqrt_two_lt_three)

/-! ## D. Falsification: the domination hypothesis `K ≤ k` is essential -/

/-- Dropping `K ≤ k` on `(0,T)` makes the acceptance sentence false: `k ≡ 1`, `K = 2`,
`u = jacobiSol 1 = sin` satisfies every remaining hypothesis on `(0,3)` with `B = 1`,
`t₀ = 1/12` (including positivity, since `3 < π`), but `3 > π/√2`. -/
theorem inv6_hk_necessary :
    ¬ (∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
        0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
        JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
        (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
        (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K →
        (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 → T ≤ Real.pi / Real.sqrt K) := by
  intro H
  have h := H (k := fun _ : ℝ => 1) (u := jacobiSol 1) (du := jacobiDeriv 1)
    (ddu := fun t => -(1 * jacobiSol 1 t)) (T := 3) (B := 1)
    (t₀ := 1 / 12) (K := 2)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (jacobiSol_jacobiSolutionOn 1 3)
    (((continuous_const.mul (continuous_jacobiSol 1)).neg).continuousOn)
    inv6_jacobiSolOne_abs_second_deriv_le_one
    (jacobiSol_zero 1) (jacobiDeriv_zero 1)
    (fun t ht => jacobiSol_pos_of_nonneg (K := 1) (by norm_num) ht.1
      (Or.inr (by
        rw [Real.sqrt_one, one_mul]
        linarith [ht.2, Real.pi_gt_three])))
    (by norm_num)
    (by
      have hmax : max (1 / Real.sqrt 2) (3 : ℝ) = 3 := by
        rw [max_eq_right]
        rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      rw [hmax]
      norm_num)
  exact absurd h (not_le.mpr inv6_pi_div_sqrt_two_lt_three)

/-! ## E. New near-threshold witness at `k ≡ K = 4` -/

/-- Positivity of `jacobiSol 4` on `(0, 314159/200000]`: `2t ≤ 3.14159 < π`. -/
theorem inv6_jacobiSolFour_pos :
    ∀ t ∈ Ioc (0 : ℝ) (314159 / 200000), 0 < jacobiSol 4 t := by
  intro t ht
  refine jacobiSol_pos_of_nonneg (K := 4) (by norm_num) ht.1 (Or.inr ?_)
  rw [inv6_sqrt_four]
  have hle : 2 * t ≤ 2 * ((314159 : ℝ) / 200000) :=
    mul_le_mul_of_nonneg_left ht.2 (by norm_num)
  have hpi : 2 * ((314159 : ℝ) / 200000) < Real.pi := by
    have h := Real.pi_gt_d6
    norm_num at h ⊢
    linarith
  linarith

/-- Second-derivative bound for `jacobiSol 4` with `B = 2` on `(0, 314159/200000)`. -/
theorem inv6_jacobiSolFour_abs_second_deriv_le_two :
    ∀ t ∈ Ioo (0 : ℝ) (314159 / 200000), |(-(4 * jacobiSol 4 t))| ≤ 2 := by
  intro t _ht
  rw [jacobiSol_of_pos (by norm_num : (0 : ℝ) < 4), jacobiSolSphere, inv6_sqrt_four]
  have hsin : |Real.sin (2 * t)| ≤ 1 := Real.abs_sin_le_one _
  have hrew : |(-(4 * (Real.sin (2 * t) / 2)))| = 2 * |Real.sin (2 * t)| := by
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hrew]
  linarith

/-- `B t₀ ≤ 1/2` and the model threshold for the `k ≡ K = 4`, `T = 314159/200000`,
`B = 2`, `t₀ = 1/13` instance: `4·T·(1/13) = 6.28318/13 < 1/2`. -/
theorem inv6_jacobiSolFour_model_threshold :
    (4 * max (1 / Real.sqrt 4) ((314159 : ℝ) / 200000)) * (1 / 13) ≤ 1 / 2 := by
  have hmax : max (1 / Real.sqrt 4) ((314159 : ℝ) / 200000) = (314159 : ℝ) / 200000 := by
    rw [max_eq_right]
    rw [inv6_sqrt_four]
    norm_num
  rw [hmax]
  norm_num

/-- **New near-threshold witness (`k ≡ K = 4`).**  The solution `jacobiSol 4` with
`T = 314159/200000 = 1.570795`, `B = 2`, `t₀ = 1/13` satisfies every hypothesis of the
endpoint bound, giving `T < π/√4 = π/2`.  Since `T/(π/√4) = 3.14159/π > 0.9999991`, the
bound is met essentially at the sharp threshold `π/2 = 1.5707963…` by a genuine solution,
with the strict form of the theorem. -/
theorem inv6_near_threshold_witness_strict :
    (314159 : ℝ) / 200000 < Real.pi / Real.sqrt 4 :=
  conjugate_point_bound_strict (T := 314159 / 200000) (B := 2) (t₀ := 1 / 13) (K := 4)
    (k := fun _ : ℝ => 4) (u := jacobiSol 4) (du := jacobiDeriv 4)
    (ddu := fun t => -(4 * jacobiSol 4 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 4 (314159 / 200000))
    (((continuous_const.mul (continuous_jacobiSol 4)).neg).continuousOn)
    inv6_jacobiSolFour_abs_second_deriv_le_two
    (jacobiSol_zero 4) (jacobiDeriv_zero 4)
    inv6_jacobiSolFour_pos
    (by norm_num) (fun _ _ => by norm_num)
    inv6_jacobiSolFour_model_threshold

/-- The non-strict endpoint form of the new near-threshold witness. -/
theorem inv6_near_threshold_witness :
    (314159 : ℝ) / 200000 ≤ Real.pi / Real.sqrt 4 :=
  le_of_lt inv6_near_threshold_witness_strict

/-- The threshold form of the new witness: `π/√4 = π/2` and `3.14159 < π`, so
`T = 314159/200000` lies below the sharp threshold by `2.65·10⁻⁶`. -/
theorem inv6_threshold_gap : Real.pi / Real.sqrt 4 - (314159 : ℝ) / 200000 > 0 := by
  rw [inv6_sqrt_four]
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  linarith

end Poincare.L4.GeodesicComparison

/-! ## F. Axiom cones of the invocation-6 probe declarations -/

#print axioms Poincare.L4.GeodesicComparison.inv6_statement_fidelity
#print axioms Poincare.L4.GeodesicComparison.inv6_pi_div_sqrt_two_lt_three
#print axioms Poincare.L4.GeodesicComparison.inv6_sqrt_four
#print axioms Poincare.L4.GeodesicComparison.inv6_jacobiSolTwo_abs_second_deriv_le_sqrt_two
#print axioms Poincare.L4.GeodesicComparison.inv6_jacobiSolOne_abs_second_deriv_le_one
#print axioms Poincare.L4.GeodesicComparison.inv6_hpos_necessary
#print axioms Poincare.L4.GeodesicComparison.inv6_hk_necessary
#print axioms Poincare.L4.GeodesicComparison.inv6_jacobiSolFour_pos
#print axioms Poincare.L4.GeodesicComparison.inv6_jacobiSolFour_abs_second_deriv_le_two
#print axioms Poincare.L4.GeodesicComparison.inv6_jacobiSolFour_model_threshold
#print axioms Poincare.L4.GeodesicComparison.inv6_near_threshold_witness_strict
#print axioms Poincare.L4.GeodesicComparison.inv6_near_threshold_witness
#print axioms Poincare.L4.GeodesicComparison.inv6_threshold_gap
