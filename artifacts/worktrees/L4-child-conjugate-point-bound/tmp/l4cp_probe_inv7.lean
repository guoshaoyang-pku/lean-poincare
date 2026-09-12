/-
Invocation-7 independent probe for the L4 conjugate-point-bound deliverable.

This file is NOT part of the release package.  It is a consumer-side, independently
written probe compiled against the frozen oleans of
`Poincare.L4.GeodesicComparison.ConjugatePointEndpoint`.

New relative to the probes of invocations 2-6:

* `inv7_statement_fidelity` ascribes the acceptance sentence (written out by hand)
  against the deliverable's `conjugate_point_bound`.
* `inv7_nonconstant_witness` / `inv7_nonconstant_witness_strict` instantiate the
  general theorem with a genuinely **non-constant** coefficient
  `inv7k t = 2 / (t * (4 - t)) ≥ 1/2` on `(0,2)` and the exact solution
  `inv7u t = t - t^2/4` of `u'' = -inv7k · u` with `u 0 = 0`, `u' 0 = 1`.
  Every previous witness in this task used a constant coefficient (`k ≡ 2,3,4,5`),
  so this is the first instantiation that exercises the non-constant part of
  `JacobiSolutionOn k u du ddu` and of the domination hypothesis `K ≤ k`.
* `inv7_k_nonconstant` certifies `inv7k` is not constant.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointEndpoint

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- The acceptance sentence of the task, written out independently (all hypotheses in the
order of the acceptance text; `hzero` of `rauch_upper_of_jacobi_constCurv` removed and
replaced by `0 < K`). -/
def Inv7HeadlineType : Prop :=
  ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
    0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
    JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
    (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
    (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 →
    T ≤ Real.pi / Real.sqrt K

/-- Statement fidelity: the deliverable's type is definitionally equal to the independently
written acceptance sentence. -/
theorem inv7_statement_fidelity : Inv7HeadlineType := conjugate_point_bound

/-! ## A non-constant-coefficient Jacobi solution on `(0,2)` -/

/-- A coefficient that is non-constant and satisfies `1/2 ≤ inv7k t` on `(0,2)`. -/
def inv7k (t : ℝ) : ℝ := 2 / (t * (4 - t))

/-- The exact solution `t - t²/4 = t(4-t)/4` of `u'' = -inv7k · u` with `u 0 = 0`,
`u' 0 = 1`; positive on `(0,2]` (its next zero is at `t = 4`). -/
def inv7u (t : ℝ) : ℝ := t - t ^ 2 / 4

def inv7du (t : ℝ) : ℝ := 1 - t / 2

def inv7ddu (_ : ℝ) : ℝ := -(1 / 2)

/-- `inv7k` is not constant (e.g. `inv7k 1 = 2/3` while `inv7k 2 = 1/2`). -/
theorem inv7_k_nonconstant : inv7k 1 ≠ inv7k 2 := by
  norm_num [inv7k]

theorem inv7_hasDerivAt_u ⦃t : ℝ⦄ (_ht : t ∈ Ioo (0 : ℝ) 2) :
    HasDerivAtR inv7u (inv7du t) t := by
  change HasDerivAtR (fun s : ℝ => s - s ^ 2 / 4) (1 - t / 2) t
  have h2 : HasDerivAtR (fun s : ℝ => s ^ 2 / 4) (t / 2) t := by
    have h : HasDerivAtR (fun s : ℝ => s ^ 2) (2 * t) t := by
      have h0 := hasDerivAtR_pow 2 t
      convert h0 using 1
      ring
    have h' : HasDerivAtR (fun s : ℝ => s ^ 2 / 4) (2 * t / 4) t := h.div_const 4
    convert h' using 1
    ring
  have h : HasDerivAtR (fun s : ℝ => s - s ^ 2 / 4) (1 - t / 2) t :=
    (hasDerivAtR_id t).sub h2
  exact h

theorem inv7_hasDerivAt_du ⦃t : ℝ⦄ (_ht : t ∈ Ioo (0 : ℝ) 2) :
    HasDerivAtR inv7du (inv7ddu t) t := by
  change HasDerivAtR (fun s : ℝ => 1 - s / 2) (-(1 / 2)) t
  have h : HasDerivAtR (fun s : ℝ => 1 - s / 2) (0 - 1 / 2) t :=
    (hasDerivAtR_const (1 : ℝ) t).sub ((hasDerivAtR_id t).div_const 2)
  convert h using 1
  ring

theorem inv7_eq_secondDeriv ⦃t : ℝ⦄ (ht : t ∈ Ioo (0 : ℝ) 2) :
    inv7ddu t = -(inv7k t) * inv7u t := by
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have h4t : 4 - t ≠ 0 := by linarith [ht.2]
  have hden : t * (4 - t) ≠ 0 := mul_ne_zero ht0 h4t
  simp only [inv7ddu, inv7k, inv7u]
  field_simp [hden]
  ring

theorem inv7_continuousOn_u : ContinuousOn inv7u (Icc (0 : ℝ) 2) := by
  change ContinuousOn (fun s : ℝ => s - s ^ 2 / 4) (Icc (0 : ℝ) 2)
  fun_prop

theorem inv7_continuousOn_du : ContinuousOn inv7du (Icc (0 : ℝ) 2) := by
  change ContinuousOn (fun s : ℝ => 1 - s / 2) (Icc (0 : ℝ) 2)
  fun_prop

/-- The explicit solution is a `JacobiSolutionOn` for the non-constant coefficient
`inv7k` on `(0,2)`. -/
theorem inv7_jacobiSolution :
    JacobiSolutionOn inv7k inv7u inv7du inv7ddu 0 2 where
  hasDerivAt_u := inv7_hasDerivAt_u
  hasDerivAt_du := inv7_hasDerivAt_du
  eq_secondDeriv := inv7_eq_secondDeriv
  continuousOn_u := inv7_continuousOn_u
  continuousOn_du := inv7_continuousOn_du

theorem inv7_u_pos : ∀ t ∈ Ioc (0 : ℝ) 2, 0 < inv7u t := by
  intro t ht
  have h : inv7u t = t * (4 - t) / 4 := by
    simp only [inv7u]
    ring
  rw [h]
  exact div_pos (mul_pos ht.1 (by linarith [ht.2])) (by norm_num)

/-- The non-constant coefficient dominates `K = 1/2` on all of `(0,2)`. -/
theorem inv7_k_ge : ∀ t ∈ Ioo (0 : ℝ) 2, (1 / 2 : ℝ) ≤ inv7k t := by
  intro t ht
  have hden : 0 < t * (4 - t) := mul_pos ht.1 (by linarith [ht.2])
  have hle : t * (4 - t) ≤ 4 := by nlinarith [sq_nonneg (t - 2)]
  have h1 : (1 : ℝ) / 2 ≤ 2 / (t * (4 - t)) := by
    rw [le_div_iff₀ hden]
    have h2 : (1 / 2 : ℝ) * (t * (4 - t)) ≤ (1 / 2 : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    linarith
  simpa only [inv7k] using h1

theorem inv7_ddu_bound : ∀ t ∈ Ioo (0 : ℝ) 2, |inv7ddu t| ≤ 1 := by
  intro t _
  norm_num [inv7ddu]

/-- Second-derivative continuity of the constant `inv7ddu`. -/
theorem inv7_ddu_continuous : ContinuousOn inv7ddu (Icc (0 : ℝ) 2) := by
  change ContinuousOn (fun _ : ℝ => -(1 / 2)) (Icc (0 : ℝ) 2)
  fun_prop

/-- **First non-constant-coefficient witness.**  The general endpoint bound applied to the
non-constant coefficient `inv7k t = 2/(t(4-t)) ≥ 1/2` and the exact solution `inv7u`
yields `2 ≤ π/√(1/2) = π√2`. -/
theorem inv7_nonconstant_witness : (2 : ℝ) ≤ Real.pi / Real.sqrt (1 / 2) := by
  have hsqrt2le : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsqrtinv : Real.sqrt ((1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.sqrt_inv]
  have hone : 1 / Real.sqrt ((1 : ℝ) / 2) = Real.sqrt 2 := by
    rw [hsqrtinv, one_div, inv_inv]
  have hmax : max (1 / Real.sqrt ((1 : ℝ) / 2)) (2 : ℝ) = 2 := by
    rw [hone, max_eq_right hsqrt2le]
  have hBmodel : ((1 : ℝ) / 2 * max (1 / Real.sqrt ((1 : ℝ) / 2)) 2) * (1 / 2) ≤ 1 / 2 := by
    rw [hmax]
    norm_num
  exact conjugate_point_bound (T := 2) (B := 1) (t₀ := 1 / 2) (K := 1 / 2)
    (k := inv7k) (u := inv7u) (du := inv7du) (ddu := inv7ddu)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    inv7_jacobiSolution inv7_ddu_continuous inv7_ddu_bound
    (by norm_num [inv7u]) (by norm_num [inv7du])
    inv7_u_pos (by norm_num) inv7_k_ge hBmodel

/-- The strict form of the same non-constant-coefficient witness: `2 < π√2`. -/
theorem inv7_nonconstant_witness_strict : (2 : ℝ) < Real.pi / Real.sqrt (1 / 2) := by
  have hsqrt2le : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsqrtinv : Real.sqrt ((1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.sqrt_inv]
  have hone : 1 / Real.sqrt ((1 : ℝ) / 2) = Real.sqrt 2 := by
    rw [hsqrtinv, one_div, inv_inv]
  have hmax : max (1 / Real.sqrt ((1 : ℝ) / 2)) (2 : ℝ) = 2 := by
    rw [hone, max_eq_right hsqrt2le]
  have hBmodel : ((1 : ℝ) / 2 * max (1 / Real.sqrt ((1 : ℝ) / 2)) 2) * (1 / 2) ≤ 1 / 2 := by
    rw [hmax]
    norm_num
  exact conjugate_point_bound_strict (T := 2) (B := 1) (t₀ := 1 / 2) (K := 1 / 2)
    (k := inv7k) (u := inv7u) (du := inv7du) (ddu := inv7ddu)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    inv7_jacobiSolution inv7_ddu_continuous inv7_ddu_bound
    (by norm_num [inv7u]) (by norm_num [inv7du])
    inv7_u_pos (by norm_num) inv7_k_ge hBmodel

/-- Sanity: the numeric inequality obtained is genuinely nontrivial (`2 < π√2`). -/
theorem inv7_bound_is_nontrivial : (2 : ℝ) < Real.pi * Real.sqrt 2 := by
  have h := inv7_nonconstant_witness_strict
  have hsqrtinv : Real.sqrt ((1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.sqrt_inv]
  rwa [hsqrtinv, div_inv_eq_mul] at h

end Poincare.L4.GeodesicComparison

/-! ## Axiom cones of every new declaration (must be exactly the allowed triple) -/

#print axioms Poincare.L4.GeodesicComparison.inv7_statement_fidelity
#print axioms Poincare.L4.GeodesicComparison.inv7_k_nonconstant
#print axioms Poincare.L4.GeodesicComparison.inv7_hasDerivAt_u
#print axioms Poincare.L4.GeodesicComparison.inv7_hasDerivAt_du
#print axioms Poincare.L4.GeodesicComparison.inv7_eq_secondDeriv
#print axioms Poincare.L4.GeodesicComparison.inv7_continuousOn_u
#print axioms Poincare.L4.GeodesicComparison.inv7_continuousOn_du
#print axioms Poincare.L4.GeodesicComparison.inv7_jacobiSolution
#print axioms Poincare.L4.GeodesicComparison.inv7_u_pos
#print axioms Poincare.L4.GeodesicComparison.inv7_k_ge
#print axioms Poincare.L4.GeodesicComparison.inv7_ddu_bound
#print axioms Poincare.L4.GeodesicComparison.inv7_ddu_continuous
#print axioms Poincare.L4.GeodesicComparison.inv7_nonconstant_witness
#print axioms Poincare.L4.GeodesicComparison.inv7_nonconstant_witness_strict
#print axioms Poincare.L4.GeodesicComparison.inv7_bound_is_nontrivial
