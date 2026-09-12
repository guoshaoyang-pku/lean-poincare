/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — Sturm zero counting for the scalar Jacobi equation

`Poincare.D12.ComparisonGeodesics.SturmComparison` proves the abstract Sturm comparison
theorem: if `k₂ ≤ k₁` on `[a,b]`, `uᵢ'' + kᵢ uᵢ = 0`, `u₁ a = u₂ a = 0`, `u₂ b = 0` and
`u₂ > 0` on `(a,b)`, then either `u₁` has a zero in `(a,b)` or `k₁ = k₂` identically there.

This file *consumes* that engine with **constructed** model data: the shifted
constant-curvature model `t ↦ sin (√K (t - a))`, whose Jacobi-solution structure, endpoint
derivative and positivity are all proved here.  The resulting zero-counting statement is:

* `exists_jacobi_zero_of_curvature_gt` — if `k ≥ K > 0` on `[a,b]`, `u` is a Jacobi solution
  with `u a = 0`, and `k > K` at some interior point, and `√K (b - a) = π`, then `u` has a zero
  in `(a,b)`.  In words: a strict curvature excess forces the unknown solution to vanish
  strictly before the model's first zero.
* `exists_jacobi_zero_before_pi_sqrt` — the anchored form: for `k ≥ K > 0` and `u 0 = 0`, a
  strict excess `k > K` somewhere in `(0, π/√K)` forces a zero of `u` in `(0, π/√K)`.  This is
  the strict, existence-half companion of the round-2 positivity bound
  `conjugate_point_bound` (`u > 0` on `(0,T]` implies `T ≤ π/√K`): whenever `k` strictly
  exceeds `K` somewhere, `u` vanishes strictly before the model's first zero.
* Witnesses: the explicit zero `sin (√2 · π/√2) = sin π = 0` inside `(0,π)` for `k = 2`, `K = 1`;
  and `sin_no_zero_in_Ioo_zero_pi`, which shows the strictness hypothesis is not removable
  (for `k ≡ K = 1` the model has no zero in `(0,π)`).

Everything is scalar ODE data.  No manifold-level zero-counting or geodesic statement is
claimed; the geometric interpretation (zeros of Jacobi fields and conjugate points) is the
unformalized U3 bridge.
-/
import Poincare.D12.ComparisonGeodesics.SturmComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics

/-! ## 1. The shifted constant-curvature model -/

/-- The shifted constant-curvature model `t ↦ sin (√K (t - a))`.  For `K > 0` its first zero
to the right of `a` is at `a + π/√K`; for `K ≤ 0` (where Lean's `Real.sqrt K = 0`) the model is
identically zero and the zero theorems below do not apply. -/
noncomputable def sturmModel (K a t : ℝ) : ℝ := Real.sin (Real.sqrt K * (t - a))

/-- The derivative of `sturmModel`. -/
noncomputable def sturmModelDeriv (K a t : ℝ) : ℝ :=
  Real.sqrt K * Real.cos (Real.sqrt K * (t - a))

/-- The second derivative of `sturmModel`. -/
noncomputable def sturmModelSecondDeriv (K a t : ℝ) : ℝ :=
  -(K * Real.sin (Real.sqrt K * (t - a)))

/-- Derivative of the shifted model. -/
theorem hasDerivAtR_sturmModel (K a t : ℝ) :
    HasDerivAtR (sturmModel K a) (sturmModelDeriv K a t) t := by
  unfold sturmModel sturmModelDeriv HasDerivAtR
  have h : HasDerivAt (fun s : ℝ => Real.sqrt K * (s - a)) (Real.sqrt K) t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_mul (Real.sqrt K)
  have hsin := (Real.hasDerivAt_sin (Real.sqrt K * (t - a))).comp t h
  have hfun : (Real.sin ∘ fun s : ℝ => Real.sqrt K * (s - a))
      = fun s : ℝ => Real.sin (Real.sqrt K * (s - a)) := rfl
  rw [hfun] at hsin
  simpa [mul_comm] using hsin

/-- Derivative of the derivative of the shifted model; this is where `0 ≤ K` is used
(`√K · √K = K`). -/
theorem hasDerivAtR_sturmModelDeriv {K a t : ℝ} (hK : 0 ≤ K) :
    HasDerivAtR (sturmModelDeriv K a) (sturmModelSecondDeriv K a t) t := by
  unfold sturmModelDeriv sturmModelSecondDeriv HasDerivAtR
  have h : HasDerivAt (fun s : ℝ => Real.sqrt K * (s - a)) (Real.sqrt K) t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_mul (Real.sqrt K)
  have hc := (Real.hasDerivAt_cos (Real.sqrt K * (t - a))).comp t h
  have hmul := hc.const_mul (Real.sqrt K)
  have hgoal : Real.sqrt K * (-(Real.sin (Real.sqrt K * (t - a))) * Real.sqrt K)
      = -(K * Real.sin (Real.sqrt K * (t - a))) := by
    have hs : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK
    calc Real.sqrt K * (-(Real.sin (Real.sqrt K * (t - a))) * Real.sqrt K)
        = -(Real.sin (Real.sqrt K * (t - a)) * (Real.sqrt K * Real.sqrt K)) := by ring
      _ = -(Real.sin (Real.sqrt K * (t - a)) * K) := by rw [hs]
      _ = -(K * Real.sin (Real.sqrt K * (t - a))) := by ring
  rw [hgoal] at hmul
  exact hmul

/-- The shifted constant-curvature model is a Jacobi solution for constant curvature `K ≥ 0`. -/
theorem sturmModel_jacobiSolutionOn {K a b : ℝ} (hK : 0 ≤ K) :
    JacobiSolutionOn (fun _ => K) (sturmModel K a) (sturmModelDeriv K a)
      (sturmModelSecondDeriv K a) a b where
  hasDerivAt_u := fun t _ => hasDerivAtR_sturmModel K a t
  hasDerivAt_du := fun t _ => hasDerivAtR_sturmModelDeriv (K := K) (a := a) hK
  eq_secondDeriv := by
    intro t _
    simp only [sturmModelSecondDeriv, sturmModel]
    ring
  continuousOn_u := by
    unfold sturmModel
    fun_prop
  continuousOn_du := by
    unfold sturmModelDeriv
    fun_prop

/-- Positivity of the shifted model before its first zero. -/
theorem sturmModel_pos {K a b t : ℝ} (hK : 0 < K) (hspan : Real.sqrt K * (b - a) = Real.pi)
    (ht : t ∈ Ioo a b) : 0 < sturmModel K a t := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have h1 : 0 < Real.sqrt K * (t - a) := mul_pos hsqrt (by linarith [ht.1])
  have h2 : Real.sqrt K * (t - a) < Real.pi :=
    calc Real.sqrt K * (t - a) < Real.sqrt K * (b - a) :=
          mul_lt_mul_of_pos_left (by linarith [ht.2]) hsqrt
      _ = Real.pi := hspan
  simpa [sturmModel] using Real.sin_pos_of_pos_of_lt_pi h1 h2

/-! ## 2. The zero-counting theorem -/

/-- **Strict curvature excess forces a zero before the model's zero.**  Let `K > 0`, let
`k ≥ K` on `[a,b]` with `k > K` at some interior point, let `u` solve `u'' + k u = 0` on
`(a,b)` with `u a = 0`, and suppose `b` is exactly the first zero `a + π/√K` of the shifted
constant-curvature model.  Then `u` has a zero in `(a,b)`.

Proof: apply the D12 Sturm engine with `u₂` the constructed shifted model; the alternative
`k = K` on `(a,b)` is excluded by the strict excess. -/
theorem exists_jacobi_zero_of_curvature_gt {k : ℝ → ℝ} {K a b : ℝ} {u du ddu : ℝ → ℝ}
    (hab : a < b) (hK : 0 < K) (hspan : Real.sqrt K * (b - a) = Real.pi)
    (hk : ∀ t ∈ Icc a b, K ≤ k t)
    (h : JacobiSolutionOn k u du ddu a b) (hua : u a = 0)
    (hstrict : ∃ t ∈ Ioo a b, K < k t) :
    ∃ c ∈ Ioo a b, u c = 0 := by
  have hmodel := sturmModel_jacobiSolutionOn (K := K) (a := a) (b := b) hK.le
  have hmodelpos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < sturmModel K a t :=
    fun t ht => sturmModel_pos hK hspan ht
  have hua' : sturmModel K a a = 0 := by simp [sturmModel]
  have hub : sturmModel K a b = 0 := by
    simp only [sturmModel]
    rw [hspan, Real.sin_pi]
  have hmain := sturm_zero_comparison (k₁ := k) (k₂ := fun _ : ℝ => K) (u₁ := u) (du₁ := du)
    (ddu₁ := ddu) (u₂ := sturmModel K a) (du₂ := sturmModelDeriv K a)
    (ddu₂ := sturmModelSecondDeriv K a) hab
    (fun t ht => hk t ht) h hmodel hua hua' hub hmodelpos
    (hasDerivAtR_sturmModel K a b)
  rcases hmain with hzero | heq
  · exact hzero
  · obtain ⟨t, ht, hlt⟩ := hstrict
    exact absurd (heq ht) (ne_of_gt hlt)

/-- **Anchored form at `0`.**  For `k ≥ K > 0`, a Jacobi solution with `u 0 = 0` whose
curvature strictly exceeds `K` somewhere in `(0, π/√K)` has a zero in `(0, π/√K)`. -/
theorem exists_jacobi_zero_before_pi_sqrt {k : ℝ → ℝ} {K : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K)
    (hk : ∀ t ∈ Icc 0 (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0)
    (hstrict : ∃ t ∈ Ioo 0 (Real.pi / Real.sqrt K), K < k t) :
    ∃ c ∈ Ioo 0 (Real.pi / Real.sqrt K), u c = 0 := by
  refine exists_jacobi_zero_of_curvature_gt (K := K) (a := 0) (b := Real.pi / Real.sqrt K)
    (by positivity) hK ?_ hk h hu0 hstrict
  rw [sub_zero]
  exact mul_div_cancel₀ Real.pi (Real.sqrt_pos_of_pos hK).ne'

/-- **The dichotomy form.**  If `u` has *no* zero in `(0, π/√K)`, then the curvature must equal
`K` identically there: the only way to avoid the zero forced by
`exists_jacobi_zero_before_pi_sqrt` is the equality case of the Sturm alternative. -/
theorem eq_curvature_of_no_jacobi_zero_before_pi_sqrt {k : ℝ → ℝ} {K : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K)
    (hk : ∀ t ∈ Icc 0 (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0)
    (hno : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), u t ≠ 0) :
    ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), k t = K := by
  intro t ht
  by_contra hne
  have hlt : K < k t :=
    lt_of_le_of_ne (hk t (Ioo_subset_Icc_self ht)) (Ne.symm hne)
  obtain ⟨c, hc, hzero⟩ :=
    exists_jacobi_zero_before_pi_sqrt hK hk h hu0 ⟨t, ht, hlt⟩
  exact hno c hc hzero

/-! ## 3. Witnesses -/

/-- **Explicit zero witness.**  `π/√2` lies in `(0,π)` and is a zero of `sin (√2 ·)`, the
solution with `k = 2`; this is the zero whose existence
`exists_jacobi_zero_of_curvature_gt` predicts against the model `K = 1` on `(0,π)`. -/
theorem sin_sqrt_two_explicit_zero :
    Real.pi / Real.sqrt 2 ∈ Ioo (0 : ℝ) Real.pi ∧
      Real.sin (Real.sqrt 2 * (Real.pi / Real.sqrt 2)) = 0 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  constructor
  · constructor
    · positivity
    · rw [div_lt_iff₀ hsqrt]
      nlinarith [Real.pi_pos, Real.one_lt_sqrt_two]
  · rw [mul_div_cancel₀ _ hsqrt.ne', Real.sin_pi]

/-- **Non-vacuity of the main theorem.**  The `k = 2`, `K = 1` instance on `(0,π)` satisfies
every hypothesis of `exists_jacobi_zero_of_curvature_gt`, and its conclusion is the genuinely
nontrivial existence of a zero of `sin (√2 ·)` in `(0,π)`, exhibited explicitly at `π/√2`. -/
theorem sturm_zero_curvature_witness :
    ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin (Real.sqrt 2 * c) = 0 := by
  have hK : (0 : ℝ) < 1 := by norm_num
  have hmain := exists_jacobi_zero_of_curvature_gt (K := 1) (a := 0) (b := Real.pi)
    (k := fun _ : ℝ => 2) (u := sturmModel 2 0) (du := sturmModelDeriv 2 0)
    (ddu := sturmModelSecondDeriv 2 0) Real.pi_pos hK
    (by rw [Real.sqrt_one, one_mul, sub_zero])
    (fun t _ => by norm_num)
    (sturmModel_jacobiSolutionOn (K := 2) (a := 0) (b := Real.pi) (by norm_num))
    (by simp [sturmModel])
    ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, by norm_num⟩
  simpa [sturmModel] using hmain

/-- **The strictness hypothesis is not removable.**  For `k ≡ K = 1` the model `sin` has no
zero in `(0,π)`: the alternative `k = K` in the Sturm engine is a genuine alternative, not an
artifact.  Hence `exists_jacobi_zero_of_curvature_gt` cannot be strengthened by dropping
`hstrict`. -/
theorem sin_no_zero_in_Ioo_zero_pi :
    ¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c = 0 := by
  rintro ⟨c, hc, hsin⟩
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨n, rfl⟩ := hsin
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : (0 : ℝ) < (n : ℝ) := by
    have h := hc.1
    rw [mul_comm] at h
    exact pos_of_mul_pos_right h Real.pi_pos.le
  have h1' : (0 : ℤ) < n := by exact_mod_cast h1
  have h2 : (n : ℝ) < 1 := by nlinarith [hc.2, Real.pi_pos]
  have h2' : n < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- **The strictness hypothesis is necessary.**  The constant-curvature case `k ≡ K = 1` with
`u = sin` on `(0,π)` satisfies every hypothesis of
`exists_jacobi_zero_before_pi_sqrt` *except* the strict excess `hstrict`, and its conclusion
fails (there is no zero of `sin` in `(0,π)`).  Hence `hstrict` cannot be dropped: the equality
case `k ≡ K` is a genuine alternative, formalizing observation O3 of the round-3 review. -/
theorem sturm_zero_strictness_necessary :
    ∃ (k : ℝ → ℝ) (u du ddu : ℝ → ℝ),
      (∀ t ∈ Icc (0 : ℝ) Real.pi, (1 : ℝ) ≤ k t) ∧
        JacobiSolutionOn k u du ddu 0 Real.pi ∧ u 0 = 0 ∧
        ¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, u c = 0 := by
  refine ⟨fun _ => 1, sturmModel 1 0, sturmModelDeriv 1 0, sturmModelSecondDeriv 1 0,
    fun _ _ => le_rfl,
    sturmModel_jacobiSolutionOn (K := 1) (a := 0) (b := Real.pi) (by norm_num), ?_, ?_⟩
  · simp [sturmModel]
  · simpa [sturmModel] using sin_no_zero_in_Ioo_zero_pi

end Poincare.L4.GeodesicComparison
