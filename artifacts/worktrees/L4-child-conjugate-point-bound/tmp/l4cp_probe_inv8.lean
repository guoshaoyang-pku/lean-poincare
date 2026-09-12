/-
Invocation-8 independent consumer-side probe for the L4 conjugate-point-bound deliverable.

NOT part of the release package.  Compiled against the frozen oleans of
`Poincare.L4.GeodesicComparison.ConjugatePointEndpoint` with `lake env lean`.

Contents (all written from scratch in this invocation):

* `Inv8HeadlineType` / `inv8_statement_fidelity` — the acceptance sentence written out by
  hand and ascribed against the deliverable's `conjugate_point_bound`; this fails to compile
  if the deliverable's type differs by a single hypothesis or by its conclusion.
* `inv8_nonconstant_*` — a *new* non-vacuous instantiation of the general theorem with the
  non-constant coefficient `inv8k t = 2/(t(5-t))` on `(0,2)` and the exact solution
  `inv8u t = t - t²/5`, `K = 1/3`, `B = 2/5`, `t₀ = 1/4`.  Every hypothesis is discharged;
  conclusion `2 ≤ π/√(1/3) = π√3`, strict form `2 < π√3`.  (Different data from every
  witness already recorded in the task, including the inv7 probe's `2/(t(4-t))`.)
* `inv8_threshold_inadmissible` — consumer-side check that the positivity hypothesis really
  fails at the closed endpoint for the `k = 2` model.
* `#check` / `#print axioms` of the headline declarations, for raw comparison.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointEndpoint

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. Statement fidelity against a hand-written acceptance type -/

/-- The acceptance sentence of the task, written out independently: `k ≥ K > 0` on `(0,T)`,
`u 0 = 0`, `u' 0 = 1`, `u > 0` on `(0,T]`, the analytic normalization hypotheses of
`rauch_upper_of_jacobi_constCurv` (with its `hzero` replaced by `0 < K`), conclusion
`T ≤ π/√K`. -/
def Inv8HeadlineType : Prop :=
  ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
    0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
    JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
    (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
    (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 →
    T ≤ Real.pi / Real.sqrt K

/-- **Statement fidelity.**  The deliverable's theorem has *exactly* the acceptance type. -/
theorem inv8_statement_fidelity : Inv8HeadlineType := conjugate_point_bound

/-- The same check for the strict strengthening. -/
def Inv8HeadlineTypeStrict : Prop :=
  ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
    0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
    JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
    (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
    (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 →
    T < Real.pi / Real.sqrt K

theorem inv8_statement_fidelity_strict : Inv8HeadlineTypeStrict :=
  conjugate_point_bound_strict

/-! ## 2. A new non-constant-coefficient witness

`inv8u t = t - t²/5` has `inv8u 0 = 0`, `inv8u' = 1 - 2t/5`, `inv8u' 0 = 1`,
`inv8u'' = -2/5`, so it solves `u'' = -inv8k · u` for `inv8k t = 2/(t(5-t))`, which is
non-constant and `≥ 1/3` on `(0,2]` because `t(5-t)` is increasing there. -/

/-- Non-constant comparison coefficient: `2/(t(5-t))`. -/
def inv8k (t : ℝ) : ℝ := 2 / (t * (5 - t))

/-- Exact Jacobi solution with `u 0 = 0`, `u' 0 = 1`, positive on `(0,2]`. -/
def inv8u (t : ℝ) : ℝ := t - (1 / 5) * t ^ 2

/-- First derivative of `inv8u`. -/
def inv8du (t : ℝ) : ℝ := 1 - (1 / 5) * (2 * t)

/-- Second derivative of `inv8u` (constant `-2/5`). -/
def inv8ddu (_ : ℝ) : ℝ := -(2 / 5)

/-- `inv8k` is genuinely non-constant (its value at `1` differs from its value at `2`). -/
theorem inv8_k_nonconstant : inv8k 1 ≠ inv8k 2 := by
  norm_num [inv8k]

theorem inv8_jacobi : JacobiSolutionOn inv8k inv8u inv8du inv8ddu 0 2 where
  hasDerivAt_u := by
    intro t ht
    show HasDerivAtR (fun x : ℝ => x - (1 / 5) * x ^ 2) (1 - (1 / 5) * (2 * t)) t
    have h := (hasDerivAtR_id t).sub ((hasDerivAtR_pow 2 t).const_mul (1 / 5))
    norm_num at h
    exact h
  hasDerivAt_du := by
    intro t ht
    show HasDerivAtR (fun x : ℝ => 1 - (1 / 5) * (2 * x)) (-(2 / 5)) t
    have h := (hasDerivAtR_const (1 : ℝ) t).sub
      (((hasDerivAtR_id t).const_mul (2 : ℝ)).const_mul (1 / 5))
    norm_num at h
    exact h
  eq_secondDeriv := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have ht5 : (5 : ℝ) - t ≠ 0 := by
      intro h; linarith [ht.2, h]
    rw [inv8ddu, inv8k, inv8u]
    field_simp
  continuousOn_u := by
    show ContinuousOn (fun t : ℝ => t - (1 / 5) * t ^ 2) (Icc (0 : ℝ) 2)
    fun_prop
  continuousOn_du := by
    show ContinuousOn (fun t : ℝ => 1 - (1 / 5) * (2 * t)) (Icc (0 : ℝ) 2)
    fun_prop

theorem inv8_k_ge : ∀ t ∈ Ioo (0 : ℝ) 2, (1 / 3 : ℝ) ≤ inv8k t := by
  intro t ht
  have ht5 : (0 : ℝ) < t * (5 - t) := by nlinarith [ht.1, ht.2]
  have hmono : t * (5 - t) ≤ 2 * (5 - 2) := by nlinarith [ht.1, ht.2]
  rw [inv8k, le_div_iff₀ ht5]
  nlinarith [hmono]

theorem inv8_u_pos : ∀ t ∈ Ioc (0 : ℝ) 2, 0 < inv8u t := by
  intro t ht
  have h2 : (0 : ℝ) < 1 - t / 5 := by nlinarith [ht.2]
  have hmul : (0 : ℝ) < t * (1 - t / 5) := mul_pos ht.1 h2
  have heq : t * (1 - t / 5) = inv8u t := by rw [inv8u]; ring
  linarith [hmul, heq]

theorem inv8_b_bound : ∀ t ∈ Ioo (0 : ℝ) 2, |inv8ddu t| ≤ 2 / 5 := by
  intro t ht
  rw [inv8ddu]
  norm_num

theorem inv8_ddu_cont : ContinuousOn inv8ddu (Icc (0 : ℝ) 2) :=
  continuous_const.continuousOn

/-- The normalization threshold `max (1/√(1/3)) 2 = 2` used by both witnesses. -/
theorem inv8_max_eq : max (1 / Real.sqrt (1 / 3)) (2 : ℝ) = 2 := by
  rw [max_eq_right]
  rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3))]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3), Real.sqrt_nonneg (1 / 3)]

/-- **New non-vacuous witness** (non-constant coefficient): the endpoint bound at
`K = 1/3`, `T = 2` gives `2 ≤ π/√(1/3) = π√3`. -/
theorem inv8_nonconstant_witness : (2 : ℝ) ≤ Real.pi / Real.sqrt (1 / 3) :=
  conjugate_point_bound (T := 2) (B := 2 / 5) (t₀ := 1 / 4) (K := 1 / 3)
    (k := inv8k) (u := inv8u) (du := inv8du) (ddu := inv8ddu)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    inv8_jacobi inv8_ddu_cont inv8_b_bound (by norm_num [inv8u]) (by norm_num [inv8du])
    inv8_u_pos (by norm_num) inv8_k_ge (by rw [inv8_max_eq]; norm_num)

/-- The same data also gives the strict form `2 < π√3`. -/
theorem inv8_nonconstant_witness_strict : (2 : ℝ) < Real.pi / Real.sqrt (1 / 3) :=
  conjugate_point_bound_strict (T := 2) (B := 2 / 5) (t₀ := 1 / 4) (K := 1 / 3)
    (k := inv8k) (u := inv8u) (du := inv8du) (ddu := inv8ddu)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    inv8_jacobi inv8_ddu_cont inv8_b_bound (by norm_num [inv8u]) (by norm_num [inv8du])
    inv8_u_pos (by norm_num) inv8_k_ge (by rw [inv8_max_eq]; norm_num)

/-! ## 3. Consumer-side sharpness check: the closed endpoint is inadmissible -/

/-- At `T = π/√2` the positivity hypothesis for the `k = 2` model fails, so the sharp
threshold of `jacobiSol_two_pos_iff` cannot be relaxed. -/
theorem inv8_threshold_inadmissible :
    ¬ (∀ t ∈ Ioc 0 (Real.pi / Real.sqrt 2), 0 < jacobiSol 2 t) := by
  intro h
  exact absurd ((jacobiSol_two_pos_iff (Real.pi / Real.sqrt 2)).mp h) (lt_irrefl _)

/-- The `k = 2`, `K = 1` witness stated exactly as requested by the acceptance sentence. -/
theorem inv8_witness_k2_K1 : (2 : ℝ) ≤ Real.pi / Real.sqrt 1 :=
  conjugate_point_bound_witness_k2_K1

/-- The sharpened `k = 2`, `K = 2` witness. -/
theorem inv8_witness_k2_K2 : (2 : ℝ) ≤ Real.pi / Real.sqrt 2 :=
  conjugate_point_bound_witness_k2_K2

end Poincare.L4.GeodesicComparison

/-! ## 4. Raw types and axiom cones -/

open Poincare.L4.GeodesicComparison in
#check @conjugate_point_bound
open Poincare.L4.GeodesicComparison in
#check @conjugate_point_bound_witness_k2_K1
open Poincare.L4.GeodesicComparison in
#check @conjugate_point_bound_witness_k2_K2

#print axioms Poincare.L4.GeodesicComparison.inv8_statement_fidelity
#print axioms Poincare.L4.GeodesicComparison.inv8_nonconstant_witness
#print axioms Poincare.L4.GeodesicComparison.inv8_nonconstant_witness_strict
#print axioms Poincare.L4.GeodesicComparison.inv8_threshold_inadmissible
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound
