/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — zeros interlace: consuming the D12 Sturm engine with constructed Jacobi data

`Poincare.D12.ComparisonGeodesics.SturmComparison` proves the abstract Sturm comparison
theorem `sturm_zero_comparison`: if `k₂ ≤ k₁` on `[a,b]`, `uᵢ'' + kᵢ uᵢ = 0`, `u₁ a = u₂ a = 0`,
`u₂ b = 0`, `u₂ > 0` on `(a,b)`, then `u₁` has a zero in `(a,b)`, or `k₁ = k₂` there.

This file *consumes* that engine — together with its companions `wronskian_deriv` and
`wronskian_antitoneOn_of_le` — with **constructed** Jacobi data, and produces genuine
zero-interlacing statements rather than a restatement of the engine.

## Constructed data

* `modelJacobiSolutionOn` — the D10 constant-curvature model
  `(K, jacobiSol K, jacobiDeriv K, t ↦ −K·jacobiSol K t)` is a `JacobiSolutionOn` on `(0,T)`
  for every `K`, `T`, with `jacobiSol K 0 = 0`, `jacobiSol K (π/√K) = 0` for `K > 0`, and
  `jacobiSol K > 0` on `(0, π/√K)`.  The first zero and the derivative at it are computed.
* `sinJacobiSolutionOn` — `(1, sin, cos, −sin)` is a `JacobiSolutionOn` on any `(a,b)`.
* `linearJacobiSolutionOn` — `(0, t, 1, 0)` is a `JacobiSolutionOn` on `(0,T)`.
* `jacobiSolShift_jacobiSolutionOn` — the shifted model `t ↦ jacobiSol K (t − a)` is a
  `JacobiSolutionOn` on any `(a,b)`, with `jacobiSolShift_pos` giving positivity on
  `(a, a + π/√K)`.  It is used for the interlacing on every period.

## Results

* `exists_zero_of_curvature_lt` — **two-curvature interlacing**: between two consecutive
  zeros `a < b` of a positive comparison solution `u₂` with curvature `k₂`, every solution
  `u₁` with `u₁ a = 0` and curvature `k₁ ≥ k₂` that is *strictly larger somewhere* has a zero
  in `(a,b)`.  The strict excess removes the engine's equality alternative.
* `sin_zero_interlaces_half_model` — the explicit interlacing instance `k₁ = 1` (`u₁ = sin`)
  against the constructed model `u₂ = jacobiSol (1/2)` (`k₂ = 1/2`): the model's consecutive
  zeros `0, π/√(1/2)` bracket the zero `π` of `sin`, which is exhibited explicitly.
* `sin_interlaces_half_model_all` — the **infinite** version: for every integer `n`, `sin` has
  a zero strictly between the consecutive zeros `2nπ` and `2(n+1)π` of the shifted model
  `jacobiSolShift (1/4) (2nπ)`; the zeros of the two solutions interlace on every period.
* `exists_jacobi_zero_on_Ioc_pi_sqrt` — **zero counting**: for `K > 0`, `k ≥ K` on
  `[0, π/√K]` and `u 0 = 0`, the solution `u` has a zero in `(0, π/√K]`.  The equality case
  `k ≡ K` is handled by a Wronskian-constancy argument (`eq_zero_at_pi_sqrt_of_curvature_eq`),
  which is what upgrades the engine's open-interval alternative to the closed-interval bound.
  `exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound` is the ODE-intrinsic form: the
  curvature bound `k ≥ K` is needed only on the open interval `(0, π/√K)`.
* `firstPositiveZero_le_pi_sqrt` — the **first positive zero** of such a solution is at most
  `π/√K`; `exists_jacobi_zero_of_horizon` is the horizon form (a solution known only up to
  `H ≥ π/√K` already has a zero in `(0, π/√K]`); `no_positive_solution_past_pi_sqrt` — the
  sharpened positivity bound `T ≤ π/√K`, cross-checked in
  `SturmInterlacingConjugateCrossCheck.lean` against this round's `conjugate_point_bound`
  (which carries strictly more hypotheses).
* `pos_near_zero_of_normalized_initial`, `firstPositiveZero_mem_of_normalized` — for
  normalized initial data `u 0 = 0`, `u' 0 = 1`, the point `firstPositiveZero u` is a genuine
  zero of `u` (`u (firstPositiveZero u) = 0`, positive, and `u` is zero-free below it): the
  infimum in the definition of `firstPositiveZero` is attained.
* `wronskian_sin_linear_antitoneOn`, `mul_cos_le_sin`, `wronskian_deriv_sin_linear` —
  `wronskian_antitoneOn_of_le` and `wronskian_deriv` consumed with the explicit data
  `(k₁,u₁) = (1, sin)`, `(k₂,u₂) = (0, t)`, yielding `t·cos t ≤ sin t` on `[0,π]` and the
  concrete derivative `−t·sin t`.

## Semantic notes on the hypotheses

The `k₂ = 0`, `u₂ = t` data does **not** instantiate the engine on `(0,π)`: the engine
requires `u₂ b = 0`, while `t b = b ≠ 0` for `b > 0` (`linear_model_no_second_zero`), and
indeed the literal conclusion "the first positive zero of `sin` is `< π`" is *false*: `sin`
has no zero in `(0,π)` and its first positive zero is exactly `π`
(`sin_no_zero_in_Ioo_zero_pi`, `sin_first_positive_zero_is_pi`).  The linear model is
instead consumed through the Wronskian monotonicity, where it yields the true inequality
`t·cos t ≤ sin t`.  The interlacing statement for `k₂ ≤ k₁` is obtained with the constructed
model data (`u₂ = jacobiSol (1/2)` on the first period, and the shifted `k₂ = 1/4` model
`jacobiSolShift (1/4) (2nπ)` for the infinite family), whose zero structures are proved here.

## Prior art / non-duplication

`Poincare.L4.GeodesicComparison.SturmZeroCount` (read-only input) already proves the
*strict-excess existence* statement `exists_jacobi_zero_before_pi_sqrt`.  This file does not
restate it: the new content is the interlacing theorem and its explicit instance, the
closed-interval zero and the first-positive-zero bound (including the equality case
`k ≡ K`), the hypothesis-sharpened positivity bound, and the Wronskian computations.  The
already-proved `conjugate_point_bound` is neither assumed nor duplicated; it is cited and
formally compared in `SturmInterlacingConjugateCrossCheck.lean`.

Semantic class: unconditional scalar ODE comparison.  No manifold-level statement (Jacobi
fields along geodesics, conjugate points, Rauch) is claimed.
-/
import Poincare.D12.ComparisonGeodesics.SturmComparison
import Poincare.D10.JacobiConstantCurvature.Comparison

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. Constructed Jacobi data -/

/-- **The D10 constant-curvature model is a D12 Jacobi solution.**  For every real `K` and
every `T`, the data `(K, jacobiSol K, jacobiDeriv K, t ↦ −K·jacobiSol K t)` satisfies the
scalar Jacobi equation `u'' + K u = 0` with continuous `u` and `du` on `[0,T]`. -/
theorem modelJacobiSolutionOn (K T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => K) (jacobiSol K) (jacobiDeriv K)
      (fun t => -(K * jacobiSol K t)) 0 T where
  hasDerivAt_u := by intro t _; exact hasDerivAt_jacobiSol K t
  hasDerivAt_du := by intro t _; exact hasDerivAt_jacobiDeriv K t
  eq_secondDeriv := by intro t _; ring
  continuousOn_u := (continuous_jacobiSol K).continuousOn
  continuousOn_du :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn

/-- **The sine solution is a Jacobi solution for curvature `1`**, on any interval `(a,b)`. -/
theorem sinJacobiSolutionOn (a b : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => 1) Real.sin Real.cos (fun t => -Real.sin t) a b where
  hasDerivAt_u := by intro t _; simpa using Real.hasDerivAt_sin t
  hasDerivAt_du := by intro t _; simpa using Real.hasDerivAt_cos t
  eq_secondDeriv := by intro t _; simp
  continuousOn_u := Real.continuous_sin.continuousOn
  continuousOn_du := Real.continuous_cos.continuousOn

/-- **The linear solution is a Jacobi solution for curvature `0`.** -/
theorem linearJacobiSolutionOn (T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => 0) (fun t : ℝ => t) (fun _ => 1) (fun _ => 0) 0 T where
  hasDerivAt_u := by intro t _; exact hasDerivAtR_id t
  hasDerivAt_du := by intro t _; exact hasDerivAtR_const 1 t
  eq_secondDeriv := by intro t _; simp
  continuousOn_u := continuous_id.continuousOn
  continuousOn_du := continuous_const.continuousOn

/-- **Positivity of the model before its first zero.** -/
theorem modelJacobiSol_pos {K : ℝ} (hK : 0 < K) :
    ∀ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), 0 < jacobiSol K t := by
  intro t ht
  rw [jacobiSol_of_pos hK]
  refine jacobiSolSphere_pos hK ht.1 ?_
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have := mul_lt_mul_of_pos_left ht.2 hsqrt
  rwa [mul_div_cancel₀ _ hsqrt.ne'] at this

/-- **The model's first positive zero is `π/√K`.** -/
theorem modelJacobiSol_firstZero {K : ℝ} (hK : 0 < K) :
    jacobiSol K (Real.pi / Real.sqrt K) = 0 := by
  rw [jacobiSol_of_pos hK]
  exact jacobiSolSphere_firstZero hK

/-- **The model's derivative at its first zero is `−1`.**  This is the value that makes the
Wronskian at the endpoint equal to `u` itself in the equality case of the Sturm
alternative. -/
theorem modelJacobiDeriv_firstZero {K : ℝ} (hK : 0 < K) :
    jacobiDeriv K (Real.pi / Real.sqrt K) = -1 := by
  rw [jacobiDeriv_of_pos hK]
  have h : Real.sqrt K * (Real.pi / Real.sqrt K) = Real.pi :=
    mul_div_cancel₀ _ (Real.sqrt_pos_of_pos hK).ne'
  rw [h, Real.cos_pi]

/-! ## 1b. The shifted model (for interlacing on every period) -/

/-- The shifted constant-curvature model `t ↦ jacobiSol K (t − a)`: a solution of
`u'' + K u = 0` with `u a = 0` and first zero at `a + π/√K`. -/
noncomputable def jacobiSolShift (K a : ℝ) : ℝ → ℝ := jacobiSol K ∘ fun t => t - a

/-- The derivative data of the shifted model. -/
noncomputable def jacobiDerivShift (K a : ℝ) : ℝ → ℝ := jacobiDeriv K ∘ fun t => t - a

/-- Derivative of the shifted model. -/
theorem hasDerivAt_jacobiSolShift (K a t : ℝ) :
    HasDerivAtR (jacobiSolShift K a) (jacobiDerivShift K a t) t := by
  have h : HasDerivAtR (fun s : ℝ => s - a) 1 t := (hasDerivAtR_id t).sub_const a
  have h2 : HasDerivAtR (jacobiSol K ∘ fun s : ℝ => s - a) (jacobiDeriv K (t - a) * 1) t :=
    (hasDerivAt_jacobiSol K (t - a)).comp t h
  rw [mul_one] at h2
  simpa only [jacobiSolShift, jacobiDerivShift, Function.comp_apply] using h2

/-- Derivative of the derivative of the shifted model; this is where `K` enters through
`jacobiSolShift K a t = jacobiSol K (t − a)`. -/
theorem hasDerivAt_jacobiDerivShift (K a t : ℝ) :
    HasDerivAtR (jacobiDerivShift K a) (-(K * jacobiSolShift K a t)) t := by
  have h : HasDerivAtR (fun s : ℝ => s - a) 1 t := (hasDerivAtR_id t).sub_const a
  have h2 : HasDerivAtR (jacobiDeriv K ∘ fun s : ℝ => s - a)
      (-(K * jacobiSol K (t - a)) * 1) t :=
    (hasDerivAt_jacobiDeriv K (t - a)).comp t h
  rw [mul_one] at h2
  simpa only [jacobiSolShift, jacobiDerivShift, Function.comp_apply] using h2

/-- The shifted model is a `JacobiSolutionOn` on any interval `(a,b)`. -/
theorem jacobiSolShift_jacobiSolutionOn (K a b : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => K) (jacobiSolShift K a) (jacobiDerivShift K a)
      (fun t => -(K * jacobiSolShift K a t)) a b where
  hasDerivAt_u := by intro t _; exact hasDerivAt_jacobiSolShift K a t
  hasDerivAt_du := by intro t _; exact hasDerivAt_jacobiDerivShift K a t
  eq_secondDeriv := by intro t _; ring
  continuousOn_u := by
    show ContinuousOn (jacobiSol K ∘ fun t : ℝ => t - a) (Icc a b)
    exact ((continuous_jacobiSol K).comp (continuous_id.sub continuous_const)).continuousOn
  continuousOn_du := by
    show ContinuousOn (jacobiDeriv K ∘ fun t : ℝ => t - a) (Icc a b)
    exact ((continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_jacobiDeriv K s).continuousAt).comp
        (continuous_id.sub continuous_const)).continuousOn

/-- Positivity of the shifted model before its first zero `a + π/√K`. -/
theorem jacobiSolShift_pos {K a : ℝ} (hK : 0 < K) :
    ∀ t ∈ Ioo a (a + Real.pi / Real.sqrt K), 0 < jacobiSolShift K a t := by
  intro t ht
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hx : 0 < t - a := by linarith [ht.1]
  have hxpi : Real.sqrt K * (t - a) < Real.pi := by
    have h1 : t - a < Real.pi / Real.sqrt K := by linarith [ht.2]
    have h2 := mul_lt_mul_of_pos_left h1 hsqrt
    rwa [mul_div_cancel₀ _ hsqrt.ne'] at h2
  have : 0 < jacobiSol K (t - a) := by
    rw [jacobiSol_of_pos hK]
    exact jacobiSolSphere_pos hK hx hxpi
  simpa only [jacobiSolShift, Function.comp_apply] using this

/-! ## 2. The engine instantiated: two-curvature zero interlacing -/

/-- **Zero interlacing between two curvatures.**  Let `k₂ ≤ k₁` on `[a,b]`, let `u₁`, `u₂`
solve the respective Jacobi equations, let `u₂` vanish at both endpoints `a < b` and be
strictly positive in between, and let `u₁ a = 0`.  If the curvature gap is *strict* at some
interior point (`k₂ t < k₁ t`), then `u₁` has a zero strictly between the two zeros of `u₂`.
This is `sturm_zero_comparison` with the equality alternative excluded by the strict gap. -/
theorem exists_zero_of_curvature_lt {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hk : ∀ t ∈ Icc a b, k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1a : u₁ a = 0) (hu2a : u₂ a = 0) (hu2b : u₂ b = 0)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u₂ t)
    (hdu2b : HasDerivAtR u₂ (du₂ b) b)
    (hstrict : ∃ t ∈ Ioo a b, k₂ t < k₁ t) :
    ∃ c ∈ Ioo a b, u₁ c = 0 := by
  rcases sturm_zero_comparison hab hk h1 h2 hu1a hu2a hu2b hu2pos hdu2b with hzero | heq
  · exact hzero
  · obtain ⟨t, ht, hlt⟩ := hstrict
    exact absurd (heq ht) (ne_of_gt hlt)

/-- **The engine's dichotomy with the endpoint hypothesis relaxed to the open interval.**
`sturm_zero_comparison` assumes `k₂ ≤ k₁` on the closed interval `[a,b]`; its proof only
uses the open interval.  This wrapper exposes that weaker hypothesis (it replays the
engine's own case analysis through `sturm_zero_comparison_of_pos` and
`sign_constant_of_no_zero`), and is what lets the zero-counting corollary meet
`conjugate_point_bound`, whose curvature bound is stated on `(0,T)`. -/
theorem sturm_dichotomy_of_interior_bound {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1a : u₁ a = 0) (hu2a : u₂ a = 0) (hu2b : u₂ b = 0)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u₂ t)
    (hdu2b : HasDerivAtR u₂ (du₂ b) b) :
    (∃ c ∈ Ioo a b, u₁ c = 0) ∨ (∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₁ t = k₂ t) := by
  by_cases hz : ∃ c ∈ Ioo a b, u₁ c = 0
  · exact Or.inl hz
  · right
    have hnozero : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → u₁ t ≠ 0 := by
      intro t ht he
      exact hz ⟨t, ht, he⟩
    have hsign := sign_constant_of_no_zero (h1.continuousOn_u.mono Ioo_subset_Icc_self) hnozero
    rcases hsign with hpos | hneg
    · exact sturm_zero_comparison_of_pos hab hk h1 h2 hu1a hu2a hu2b hpos hu2pos hdu2b
    · have hpos' : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < -u₁ t := by
        intro t ht
        exact neg_pos.mpr (hneg ht)
      have hneg1 : JacobiSolutionOn k₁ (-u₁) (-du₁) (-ddu₁) a b := h1.neg
      have hu1a' : (-u₁) a = 0 := by rw [Pi.neg_apply, hu1a, neg_zero]
      exact sturm_zero_comparison_of_pos hab hk hneg1 h2 hu1a' hu2a hu2b hpos' hu2pos hdu2b

/-- **Explicit interlacing instance.**  With `k₁ = 1` (`u₁ = sin`) and the constructed
model `k₂ = 1/2` (`u₂ = jacobiSol (1/2)`, with consecutive zeros `0` and `π/√(1/2) = √2·π`),
the strictly larger curvature forces a zero of `sin` in between; the explicit witness `π`
is exhibited.  The two zeros genuinely interlace: `0 < π < π/√(1/2)`. -/
theorem sin_zero_interlaces_half_model :
    (∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)), Real.sin c = 0) ∧
      Real.pi ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)) := by
  have hK₂ : (0 : ℝ) < 1 / 2 := by norm_num
  have hz : 0 < Real.pi / Real.sqrt (1 / 2) :=
    div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK₂)
  have hstrict : ∃ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)), (1 / 2 : ℝ) < 1 :=
    ⟨Real.pi / Real.sqrt (1 / 2) / 2, ⟨by linarith, by linarith⟩, by norm_num⟩
  constructor
  · exact exists_zero_of_curvature_lt hz (fun t _ => by norm_num)
      (sinJacobiSolutionOn 0 _) (modelJacobiSolutionOn (1 / 2) _)
      Real.sin_zero (jacobiSol_zero (1 / 2)) (modelJacobiSol_firstZero hK₂)
      (modelJacobiSol_pos hK₂) (hasDerivAt_jacobiSol (1 / 2) _) hstrict
  · refine ⟨Real.pi_pos, ?_⟩
    rw [lt_div_iff₀ (Real.sqrt_pos_of_pos hK₂)]
    have hsqrt_lt : Real.sqrt (1 / 2) < 1 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
      norm_num
    nlinarith [Real.pi_pos]

/-- **The model's first zero is strictly after the sine's first zero.**  `jacobiSol (1/2)`
vanishes at `π/√(1/2) = √2·π`, and `sin` vanishes at `π < √2·π`: the first positive zero of
the solution with the larger curvature `k₁ = 1` comes strictly before the first positive
zero of the model with `k₂ = 1/2`. -/
theorem sin_first_zero_lt_half_model_first_zero :
    Real.sin Real.pi = 0 ∧ jacobiSol (1 / 2) (Real.pi / Real.sqrt (1 / 2)) = 0 ∧
      Real.pi < Real.pi / Real.sqrt (1 / 2) :=
  ⟨Real.sin_pi, modelJacobiSol_firstZero (by norm_num), sin_zero_interlaces_half_model.2.2⟩

/-- **Infinite two-curvature interlacing.**  For every integer `n`, `sin` (curvature `k₁ = 1`)
has a zero strictly between the consecutive zeros `2nπ` and `2(n+1)π` of the shifted model
`jacobiSolShift (1/4) (2nπ)` (curvature `k₂ = 1/4`, i.e. `2·sin((t−2nπ)/2)`).  Hence the
zeros of the higher-curvature solution interlace with the zeros of the lower-curvature model
on every period, not just on the first one. -/
theorem sin_interlaces_half_model_all (n : ℤ) :
    ∃ c ∈ Ioo (2 * (n : ℝ) * Real.pi) (2 * ((n : ℝ) + 1) * Real.pi), Real.sin c = 0 := by
  have hK₂ : (0 : ℝ) < 1 / 4 := by norm_num
  set a : ℝ := 2 * (n : ℝ) * Real.pi with hadef
  have hspan : Real.pi / Real.sqrt (1 / 4) = 2 * Real.pi := by
    have : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]; ring
  have hb : a + Real.pi / Real.sqrt (1 / 4) = 2 * ((n : ℝ) + 1) * Real.pi := by
    rw [hspan, hadef]; ring
  have hstrict : ∃ t ∈ Ioo a (a + Real.pi / Real.sqrt (1 / 4)), (1 / 4 : ℝ) < 1 := by
    refine ⟨(a + (a + Real.pi / Real.sqrt (1 / 4))) / 2, ⟨?_, ?_⟩, by norm_num⟩
    · linarith [Real.pi_pos, Real.sqrt_pos_of_pos hK₂]
    · linarith [Real.pi_pos, Real.sqrt_pos_of_pos hK₂]
  have hsin_a : Real.sin a = 0 := by
    rw [hadef, Real.sin_eq_zero_iff]
    exact ⟨2 * n, by push_cast; ring⟩
  have hmain := exists_zero_of_curvature_lt (a := a) (b := a + Real.pi / Real.sqrt (1 / 4))
    (k₁ := fun _ : ℝ => 1) (k₂ := fun _ : ℝ => 1 / 4)
    (by linarith [Real.pi_pos, hspan])
    (fun t _ => by norm_num)
    (sinJacobiSolutionOn a (a + Real.pi / Real.sqrt (1 / 4)))
    (jacobiSolShift_jacobiSolutionOn (1 / 4) a (a + Real.pi / Real.sqrt (1 / 4)))
    hsin_a (by simp [jacobiSolShift, jacobiSol_zero])
    (by
      have := modelJacobiSol_firstZero hK₂
      simpa only [jacobiSolShift, Function.comp_apply, add_sub_cancel_left] using this)
    (fun t ht => jacobiSolShift_pos hK₂ t ht)
    (hasDerivAt_jacobiSolShift (1 / 4) a (a + Real.pi / Real.sqrt (1 / 4)))
    hstrict
  rwa [hb] at hmain

/-- **Explicit witness for the infinite interlacing**: `(2n+1)π` is a zero of `sin` strictly
inside the interval `(2nπ, 2(n+1)π)` between consecutive zeros of the model `2·sin(·/2)`. -/
theorem sin_zero_in_half_model_interval (n : ℤ) :
    (2 * (n : ℝ) + 1) * Real.pi ∈ Ioo (2 * (n : ℝ) * Real.pi) (2 * ((n : ℝ) + 1) * Real.pi) ∧
      Real.sin ((2 * (n : ℝ) + 1) * Real.pi) = 0 := by
  have hpi := Real.pi_pos
  constructor
  · constructor <;> nlinarith
  · rw [Real.sin_eq_zero_iff]
    exact ⟨2 * n + 1, by push_cast; ring⟩

/-! ## 3. Zero counting: the equality case and the first-zero bound -/

/-- **The equality case produces the endpoint zero.**  If `k ≡ K` on `(0, π/√K)`, `u` is a
Jacobi solution with `u 0 = 0` on that interval, then `u` vanishes at the model's first zero
`π/√K` as well.  Proof: the Wronskian `W = u₂·u' − u·u₂'` against the model `u₂ = jacobiSol K`
has `W' = (K − k)·u·u₂ = 0` in the interior, hence is constant on `[0, π/√K]`; at the
endpoints `W 0 = 0` and `W (π/√K) = u (π/√K)` (because `u₂` vanishes and `u₂' = −1` there). -/
theorem eq_zero_at_pi_sqrt_of_curvature_eq {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K) → k t = K) :
    u (Real.pi / Real.sqrt K) = 0 := by
  set z : ℝ := Real.pi / Real.sqrt K with hzdef
  have hzpos : 0 < z := by
    rw [hzdef]
    exact div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  have hmodel := modelJacobiSolutionOn K z
  set W : ℝ → ℝ := wronskian u du (jacobiSol K) (jacobiDeriv K) with hWdef
  have hWderiv : (Ioo (0 : ℝ) z).EqOn (deriv W) 0 := by
    intro t ht
    rw [hWdef, wronskian_deriv h hmodel ht, heq ht]
    simp
  have hWdiff : DifferentiableOn ℝ W (Ioo (0 : ℝ) z) := by
    rw [hWdef]
    exact wronskian_differentiableOn h hmodel
  have hz2 : z / 2 ∈ Ioo (0 : ℝ) z := ⟨by linarith, by linarith⟩
  have hconst : ∀ x ∈ Ioo (0 : ℝ) z, ∀ y ∈ Ioo (0 : ℝ) z, W x = W y :=
    fun x hx y hy =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hWdiff hWderiv hx hy
  have hEqOn : EqOn W (fun _ => W (z / 2)) (Ioo (0 : ℝ) z) := by
    intro x hx
    exact hconst x hx (z / 2) hz2
  have hWcont : ContinuousOn W (Icc (0 : ℝ) z) := by
    rw [hWdef]
    exact wronskian_continuousOn h.continuousOn_u h.continuousOn_du
      (continuous_jacobiSol K).continuousOn
      (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn
  have hclosure : closure (Ioo (0 : ℝ) z) = Icc 0 z := closure_Ioo (ne_of_lt hzpos)
  have hEqOnIcc : EqOn W (fun _ => W (z / 2)) (Icc (0 : ℝ) z) :=
    hEqOn.of_subset_closure hWcont continuousOn_const Ioo_subset_Icc_self
      (by rw [hclosure])
  have hWz : W z = W 0 := by
    have h1 : W z = W (z / 2) := hEqOnIcc (right_mem_Icc.mpr hzpos.le)
    have h2 : W 0 = W (z / 2) := hEqOnIcc (left_mem_Icc.mpr hzpos.le)
    rw [h1, h2]
  have hmodelz : jacobiSol K z = 0 := by
    rw [hzdef]
    exact modelJacobiSol_firstZero hK
  have hmodeld : jacobiDeriv K z = -1 := by
    rw [hzdef]
    exact modelJacobiDeriv_firstZero hK
  have hW0 : W 0 = 0 := by
    rw [hWdef, wronskian]
    simp [hu0]
  have hWzval : W z = u z := by
    rw [hWdef, wronskian, hmodelz, hmodeld]
    ring
  rw [hWzval, hW0] at hWz
  exact hWz

/-- **Zero-counting corollary (closed form).**  For `K > 0`, `k ≥ K` on `[0, π/√K]`, and a
Jacobi solution `u` with `u 0 = 0`, the solution has a zero in `(0, π/√K]`.  If the zero is
not in the open interval, then the engine's alternative forces `k ≡ K`, and the equality
case supplies the endpoint zero `π/√K` by Wronskian constancy. -/
theorem exists_jacobi_zero_on_Ioc_pi_sqrt {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Icc (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K)) (hu0 : u 0 = 0) :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt K), u c = 0 := by
  have hz : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  rcases sturm_zero_comparison hz hk h (modelJacobiSolutionOn K _) hu0 (jacobiSol_zero K)
      (modelJacobiSol_firstZero hK) (modelJacobiSol_pos hK)
      (hasDerivAt_jacobiSol K _) with hzero | heq
  · obtain ⟨c, hc, hcz⟩ := hzero
    exact ⟨c, ⟨hc.1, hc.2.le⟩, hcz⟩
  · exact ⟨_, ⟨hz, le_rfl⟩, eq_zero_at_pi_sqrt_of_curvature_eq hK h hu0 heq⟩

/-- **Zero-counting corollary (interior curvature bound).**  The ODE-intrinsic form: the
curvature bound `K ≤ k` is needed only on the open interval `(0, π/√K)`, since the endpoint
values of `k` are not part of the differential equation.  The conclusion is unchanged, by the
relaxed engine dichotomy `sturm_dichotomy_of_interior_bound` together with the equality-case
endpoint zero. -/
theorem exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K)) (hu0 : u 0 = 0) :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt K), u c = 0 := by
  have hz : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  rcases sturm_dichotomy_of_interior_bound hz hk h (modelJacobiSolutionOn K _) hu0
      (jacobiSol_zero K) (modelJacobiSol_firstZero hK) (modelJacobiSol_pos hK)
      (hasDerivAt_jacobiSol K _) with hzero | heq
  · obtain ⟨c, hc, hcz⟩ := hzero
    exact ⟨c, ⟨hc.1, hc.2.le⟩, hcz⟩
  · exact ⟨_, ⟨hz, le_rfl⟩, eq_zero_at_pi_sqrt_of_curvature_eq hK h hu0 heq⟩

/-- **Zero-counting corollary (normalized initial data).**  The form stated with the
standard initial conditions `u 0 = 0`, `u' 0 = 1`.  The derivative hypothesis is not needed
for the conclusion; it is recorded to match the geometric normalization. -/
theorem exists_jacobi_zero_on_Ioc_pi_sqrt_normalized {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Icc (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0) (_hdu0 : du 0 = 1) :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt K), u c = 0 :=
  exists_jacobi_zero_on_Ioc_pi_sqrt hK hk h hu0

/-- **Strict curvature excess forces a zero strictly before the model's first zero.** -/
theorem exists_jacobi_zero_on_Ioo_pi_sqrt_of_gt {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Icc (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K)) (hu0 : u 0 = 0)
    (hstrict : ∃ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), K < k t) :
    ∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), u c = 0 := by
  have hz : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  exact exists_zero_of_curvature_lt hz hk h (modelJacobiSolutionOn K _) hu0
    (jacobiSol_zero K) (modelJacobiSol_firstZero hK) (modelJacobiSol_pos hK)
    (hasDerivAt_jacobiSol K _) hstrict

/-- **Horizon form of the zero-counting corollary.**  If the Jacobi solution is given up to
a horizon `H ≥ π/√K` (with `k ≥ K > 0` on `[0,H]`), then the horizon contains a zero in
`(0, π/√K]`: the "first positive zero, if it exists before the horizon" is at most
`π/√K`. -/
theorem exists_jacobi_zero_of_horizon {k u du ddu : ℝ → ℝ} {K H : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Icc (0 : ℝ) H, K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 H) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hH : Real.pi / Real.sqrt K ≤ H) :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt K), u c = 0 := by
  have hmono : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K) :=
    { hasDerivAt_u := fun t ht => h.hasDerivAt_u ⟨ht.1, lt_of_lt_of_le ht.2 hH⟩
      hasDerivAt_du := fun t ht => h.hasDerivAt_du ⟨ht.1, lt_of_lt_of_le ht.2 hH⟩
      eq_secondDeriv := fun t ht => h.eq_secondDeriv ⟨ht.1, lt_of_lt_of_le ht.2 hH⟩
      continuousOn_u := h.continuousOn_u.mono (Icc_subset_Icc_right hH)
      continuousOn_du := h.continuousOn_du.mono (Icc_subset_Icc_right hH) }
  exact exists_jacobi_zero_on_Ioc_pi_sqrt_normalized hK
    (fun t ht => hk t ⟨ht.1, le_trans ht.2 hH⟩) hmono hu0 hdu0

/-- The **first positive zero** of a function, as the infimum of its positive zero set.  For
a Jacobi solution with `u 0 = 0` and `k ≥ K > 0`, the next theorem shows this infimum is at
most `π/√K`, so the first positive zero exists no later than the model's. -/
noncomputable def firstPositiveZero (u : ℝ → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ u t = 0}

/-- **First positive zero bounded by `π/√K`.**  For `K > 0`, `k ≥ K` on `[0, π/√K]` and a
Jacobi solution with `u 0 = 0`, the first positive zero of `u` is at most `π/√K` (and the
positive zero set is nonempty, by `exists_jacobi_zero_on_Ioc_pi_sqrt`). -/
theorem firstPositiveZero_le_pi_sqrt {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Icc (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K)) (hu0 : u 0 = 0) :
    firstPositiveZero u ≤ Real.pi / Real.sqrt K := by
  obtain ⟨c, hc, hcz⟩ := exists_jacobi_zero_on_Ioc_pi_sqrt hK hk h hu0
  have hmem : c ∈ {t : ℝ | 0 < t ∧ u t = 0} := ⟨hc.1, hcz⟩
  have hbdd : BddBelow {t : ℝ | 0 < t ∧ u t = 0} := ⟨0, fun y hy => hy.1.le⟩
  exact le_trans (csInf_le hbdd hmem) hc.2

/-- **First positive zero bounded by `π/√K` (interior curvature bound).**  Same conclusion
as `firstPositiveZero_le_pi_sqrt`, with the curvature bound required only on `(0, π/√K)`. -/
theorem firstPositiveZero_le_pi_sqrt_of_interior_bound {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K)) (hu0 : u 0 = 0) :
    firstPositiveZero u ≤ Real.pi / Real.sqrt K := by
  obtain ⟨c, hc, hcz⟩ := exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound hK hk h hu0
  have hmem : c ∈ {t : ℝ | 0 < t ∧ u t = 0} := ⟨hc.1, hcz⟩
  have hbdd : BddBelow {t : ℝ | 0 < t ∧ u t = 0} := ⟨0, fun y hy => hy.1.le⟩
  exact le_trans (csInf_le hbdd hmem) hc.2

/-- **Positivity near `0` for normalized initial data.**  If `du 0 = 1`, then `u > 0` on a
right neighbourhood of `0`: by the fundamental theorem of calculus, `u t = ∫₀ᵗ du`, and
`du > 1/2` near `0`, so `u t ≥ t/2` for small `t`.  This is what makes `firstPositiveZero`
a genuine first zero (rather than an infimum not attained at a zero). -/
theorem pos_near_zero_of_normalized_initial {k u du ddu : ℝ → ℝ} {z : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 z) (hu0 : u 0 = 0) (hdu0 : du 0 = 1) (hz : 0 < z) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ → t ≤ z → 0 < u t := by
  have hcont_at : ContinuousWithinAt du (Icc (0 : ℝ) z) 0 :=
    h.continuousOn_du.continuousWithinAt (left_mem_Icc.mpr hz.le)
  have hev : ∀ᶠ s in 𝓝[Icc (0 : ℝ) z] 0, (1 / 2 : ℝ) < du s :=
    hcont_at (isOpen_Ioi.mem_nhds (by rw [hdu0]; norm_num))
  rw [Filter.eventually_iff, mem_nhdsWithin] at hev
  obtain ⟨s, hso, hs0, hsub⟩ := hev
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.isOpen_iff.mp hso 0 hs0
  have hdu_half : ∀ x ∈ Icc (0 : ℝ) z, x < δ₀ → (1 / 2 : ℝ) < du x := by
    intro x hx hxδ
    exact hsub ⟨hδ₀sub (Metric.mem_ball.mpr (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; exact hxδ)), hx⟩
  refine ⟨min δ₀ z, lt_min hδ₀pos hz, ?_⟩
  intro t ht htδ htz
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have hint : IntervalIntegrable du volume 0 t := by
    have hcont' : ContinuousOn du (uIcc (0 : ℝ) t) := by
      rw [uIcc_of_le ht.le]
      exact h.continuousOn_du.mono (Icc_subset_Icc_right htz)
    exact hcont'.intervalIntegrable
  have hftc : ∫ x in (0)..t, du x = u t - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le
      (h.continuousOn_u.mono (Icc_subset_Icc_right htz))
      (fun x hx => h.hasDerivAt_u ⟨hx.1, lt_of_lt_of_le hx.2 htz⟩) hint
  have hmono : ∫ x in (0)..t, (1 / 2 : ℝ) ≤ ∫ x in (0)..t, du x :=
    intervalIntegral.integral_mono_on ht.le intervalIntegrable_const hint (fun x hx =>
      le_of_lt (hdu_half x ⟨hx.1, le_trans hx.2 htz⟩ (lt_of_le_of_lt hx.2 htδ₀)))
  have hconst : ∫ x in (0)..t, (1 / 2 : ℝ) = t / 2 := by
    rw [intervalIntegral.integral_const]
    ring
  rw [hconst] at hmono
  have : u t = ∫ x in (0)..t, du x := by linarith [hftc, hu0]
  linarith [hmono, this, ht]

/-- **`firstPositiveZero` is attained and is the least positive zero.**  For `K > 0`,
`k ≥ K` on `[0, π/√K]`, a Jacobi solution with `u 0 = 0`, `u' 0 = 1`:
`u (firstPositiveZero u) = 0`, the point is strictly positive, and `u` has no zero in
`(0, firstPositiveZero u)`.  Hence "first positive zero" is a genuine zero, not merely an
infimum.  Proof: `pos_near_zero_of_normalized_initial` bounds the zero set away from `0`, so
the clipped zero set is closed and nonempty; its `sInf` is attained and equals the `sInf` of
the full positive zero set. -/
theorem firstPositiveZero_mem_of_normalized {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Icc (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1) :
    u (firstPositiveZero u) = 0 ∧ 0 < firstPositiveZero u ∧
      ∀ t ∈ Ioo (0 : ℝ) (firstPositiveZero u), u t ≠ 0 := by
  set z : ℝ := Real.pi / Real.sqrt K with hzdef
  have hz : 0 < z := by
    rw [hzdef]
    exact div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  obtain ⟨δ, hδpos, hδ⟩ := pos_near_zero_of_normalized_initial h hu0 hdu0 hz
  obtain ⟨c, hc, hczero⟩ := exists_jacobi_zero_on_Ioc_pi_sqrt hK hk h hu0
  have hcδ : δ ≤ c := by
    by_contra hlt
    exact absurd hczero (ne_of_gt (hδ c hc.1 (lt_of_not_ge hlt) hc.2))
  set S : Set ℝ := {t : ℝ | 0 < t ∧ u t = 0} with hSdef
  set S' : Set ℝ := Icc δ z ∩ (Icc (0 : ℝ) z ∩ u ⁻¹' {0}) with hS'def
  have hS'closed : IsClosed S' := by
    rw [hS'def]
    exact isClosed_Icc.inter (h.continuousOn_u.preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton)
  have hS'ne : S'.Nonempty :=
    ⟨c, ⟨⟨hcδ, hc.2⟩, ⟨⟨hc.1.le, hc.2⟩, hczero⟩⟩⟩
  have hS'bdd : BddBelow S' := ⟨δ, fun y hy => hy.1.1⟩
  have hS_bdd : BddBelow S := ⟨0, fun y hy => hy.1.le⟩
  have hmem : sInf S' ∈ S' := hS'closed.csInf_mem hS'ne hS'bdd
  have hS'sub : S' ⊆ S := fun y hy => ⟨lt_of_lt_of_le hδpos hy.1.1, hy.2.2⟩
  have hle : sInf S ≤ sInf S' :=
    le_csInf hS'ne (fun y hy => csInf_le hS_bdd (hS'sub hy))
  have hge : sInf S' ≤ sInf S := by
    refine le_csInf ⟨c, ⟨hc.1, hczero⟩⟩ ?_
    intro y hy
    rcases le_or_gt y z with hyz | hzy
    · have hyδ : δ ≤ y := by
        by_contra hlt
        exact absurd hy.2 (ne_of_gt (hδ y hy.1 (lt_of_not_ge hlt) hyz))
      exact csInf_le hS'bdd ⟨⟨hyδ, hyz⟩, ⟨⟨hy.1.le, hyz⟩, hy.2⟩⟩
    · exact le_trans (csInf_le hS'bdd ⟨⟨hcδ, hc.2⟩,
        ⟨⟨hc.1.le, hc.2⟩, hczero⟩⟩) (le_trans hc.2 hzy.le)
  have hsInfEq : sInf S' = sInf S := le_antisymm hge hle
  have hsInfS : u (sInf S) = 0 := by
    rw [← hsInfEq]
    exact hmem.2.2
  have hposS : 0 < sInf S := by
    rw [← hsInfEq]
    exact lt_of_lt_of_le hδpos hmem.1.1
  refine ⟨by simpa [firstPositiveZero, hSdef] using hsInfS, ?_, ?_⟩
  · simpa [firstPositiveZero, hSdef] using hposS
  · intro t ht htzero
    have htS : t ∈ S := ⟨ht.1, htzero⟩
    have := csInf_le hS_bdd htS
    exact absurd this (not_le.mpr ht.2)

/-- **Explicit first-zero witness.**  The solution `jacobiSol 2` (`k = 2`, with `u 0 = 0`,
`u' 0 = 1`) has `jacobiSol 2 (π/√2) = 0`, and its first positive zero is at most
`π/√2 ≤ π = π/√1` with `K = 1`: the bound `firstPositiveZero_le_pi_sqrt` is attained on the
model itself. -/
theorem firstPositiveZero_jacobiSol_two :
    jacobiSol 2 (Real.pi / Real.sqrt 2) = 0 ∧
      firstPositiveZero (jacobiSol 2) ≤ Real.pi / Real.sqrt 1 := by
  refine ⟨modelJacobiSol_firstZero (by norm_num), ?_⟩
  refine firstPositiveZero_le_pi_sqrt (K := 1) (k := fun _ : ℝ => 2) (by norm_num)
    (fun t _ => by norm_num) (modelJacobiSolutionOn 2 _) (jacobiSol_zero 2)

/-! ## 4. Wronskian monotonicity with explicit data -/

/-- **`wronskian_antitoneOn_of_le` with constructed data**: for `u₁ = sin` (`k₁ = 1`) and
`u₂ = t` (`k₂ = 0`) on `[0,π]`, the sign hypothesis `0 ≤ u₁·u₂` holds and the Wronskian
`W = t·cos t − sin t` is antitone. -/
theorem wronskian_sin_linear_antitoneOn :
    AntitoneOn (wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1)) (Icc 0 Real.pi) := by
  refine wronskian_antitoneOn_of_le Real.pi_pos.le (fun t _ => by norm_num) ?_
    (sinJacobiSolutionOn 0 Real.pi) (linearJacobiSolutionOn Real.pi)
  intro t ht
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ⟨ht.1.le, ht.2.le⟩
  have ht0 : 0 ≤ t := ht.1.le
  nlinarith

/-- **A true consequence of the `k₂ = 0`, `u₂ = t` data**: `t·cos t ≤ sin t` on `[0,π]`.
The Wronskian `t·cos t − sin t` starts at `0` and is antitone, hence is `≤ 0`.  This is the
correct way to consume the linear model, since the engine itself cannot be instantiated with
it (its right-endpoint hypothesis `u₂ b = 0` fails for every `b > 0`). -/
theorem mul_cos_le_sin {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    t * Real.cos t ≤ Real.sin t := by
  have hanti := wronskian_sin_linear_antitoneOn (left_mem_Icc.mpr Real.pi_pos.le) ht ht.1
  have hW0 : wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1) 0 = 0 := by
    simp [wronskian]
  have hWt : wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1) t
      = t * Real.cos t - Real.sin t := by
    simp [wronskian]
  rw [hW0, hWt] at hanti
  linarith

/-- **`wronskian_deriv` with constructed data**: the Wronskian derivative of the
`(1, sin)` / `(0, t)` pair is `−(t·sin t)` in the interior. -/
theorem wronskian_deriv_sin_linear {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) :
    deriv (wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1)) t
      = -(t * Real.sin t) := by
  rw [wronskian_deriv (sinJacobiSolutionOn 0 Real.pi) (linearJacobiSolutionOn Real.pi) ht]
  ring

/-- **Concrete derivative value**: at `t = π/2` the Wronskian derivative is `−π/2 < 0`,
witnessing the strict decay of `t·cos t − sin t` there. -/
theorem wronskian_deriv_sin_linear_at_pi_div_two :
    deriv (wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1)) (Real.pi / 2)
      = -(Real.pi / 2) := by
  rw [wronskian_deriv_sin_linear ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
    Real.sin_pi_div_two]
  ring

/-! ## 5. The naive `k₂ = 0` instantiation is inadmissible and its conclusion is false -/

/-- The linear model does not vanish at any positive right endpoint: the engine's hypothesis
`u₂ b = 0` fails for the data `k₂ = 0`, `u₂ = t` and every `b > 0`. -/
theorem linear_model_no_second_zero {b : ℝ} (hb : 0 < b) : (fun t : ℝ => t) b ≠ 0 :=
  ne_of_gt hb

/-- The linear model has no zero in `(0,b)` for `b > 0`, so `0` is its only zero. -/
theorem linear_model_no_interior_zero {b : ℝ} :
    ∀ t ∈ Ioo (0 : ℝ) b, (fun t : ℝ => t) t ≠ 0 := by
  intro t ht
  exact ne_of_gt ht.1

/-- **The literal `k₁ = 1`/`k₂ = 0` claim is false**: `sin` has no zero in `(0,π)`. -/
theorem sin_no_zero_in_Ioo_zero_pi :
    ¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c = 0 := by
  rintro ⟨c, hc, hsin⟩
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have h1 : (0 : ℝ) < (n : ℝ) * Real.pi := by rw [hn]; exact hc.1
  have h2 : (n : ℝ) * Real.pi < Real.pi := by rw [hn]; exact hc.2
  have hnpos : (0 : ℤ) < n := by
    have : (0 : ℝ) < (n : ℝ) := by
      rcases mul_pos_iff.mp h1 with ⟨h, _⟩ | ⟨h, h'⟩
      · exact h
      · exact absurd h' (not_lt.mpr Real.pi_pos.le)
    exact_mod_cast this
  have hnlt : n < 1 := by
    have : (n : ℝ) < 1 := by nlinarith [h2, Real.pi_pos]
    exact_mod_cast this
  omega

/-- **The first positive zero of `sin` is exactly `π`**, not `< π`: `sin` is nonzero on
`(0,π)` and vanishes at `π`. -/
theorem sin_first_positive_zero_is_pi :
    (∀ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c ≠ 0) ∧ Real.sin Real.pi = 0 :=
  ⟨fun c hc h => sin_no_zero_in_Ioo_zero_pi ⟨c, hc, h⟩, Real.sin_pi⟩

/-! ## 6. Sharpened positivity bound (cross-check input) -/

/-- **No positive Jacobi solution can pass `π/√K`.**  For `K > 0`, `k ≥ K` on `(0,T)`, and a
Jacobi solution with `u 0 = 0` that is positive on `(0,T]`, necessarily `T ≤ π/√K`.  The
proof uses the engine's dichotomy with the open-interval curvature hypothesis
(`sturm_dichotomy_of_interior_bound`): a zero in `(0, π/√K)` contradicts positivity, and the
equality case `k ≡ K` gives the endpoint zero `π/√K` by Wronskian constancy.

Compared with `Poincare.L4.GeodesicComparison.conjugate_point_bound` (this round's result,
`ConjugatePointBound.lean`), this statement needs **no** second-derivative bound, no
normalization threshold, no `t₀`, no continuity of `ddu`, and no `u' 0 = 1`; the comparison
is formalized in `SturmInterlacingConjugateCrossCheck.lean`. -/
theorem no_positive_solution_past_pi_sqrt {k u du ddu : ℝ → ℝ} {T K : ℝ}
    (_hT : 0 < T) (h : JacobiSolutionOn k u du ddu 0 T) (hu0 : u 0 = 0)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t) :
    T ≤ Real.pi / Real.sqrt K := by
  by_contra hcon
  have hzT : Real.pi / Real.sqrt K < T := not_le.mp hcon
  have hzpos : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  have hmono : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K) :=
    { hasDerivAt_u := fun t ht => h.hasDerivAt_u ⟨ht.1, lt_of_lt_of_le ht.2 hzT.le⟩
      hasDerivAt_du := fun t ht => h.hasDerivAt_du ⟨ht.1, lt_of_lt_of_le ht.2 hzT.le⟩
      eq_secondDeriv := fun t ht => h.eq_secondDeriv ⟨ht.1, lt_of_lt_of_le ht.2 hzT.le⟩
      continuousOn_u := h.continuousOn_u.mono (Icc_subset_Icc_right hzT.le)
      continuousOn_du := h.continuousOn_du.mono (Icc_subset_Icc_right hzT.le) }
  rcases sturm_dichotomy_of_interior_bound hzpos
      (fun t ht => hk t ⟨ht.1, lt_trans ht.2 hzT⟩) hmono
      (modelJacobiSolutionOn K _) hu0 (jacobiSol_zero K) (modelJacobiSol_firstZero hK)
      (modelJacobiSol_pos hK) (hasDerivAt_jacobiSol K _) with hzero | heq
  · obtain ⟨c, hc, hcz⟩ := hzero
    exact absurd hcz (ne_of_gt (hpos c ⟨hc.1, (lt_of_lt_of_le hc.2 hzT.le).le⟩))
  · have hend := eq_zero_at_pi_sqrt_of_curvature_eq hK hmono hu0 (fun t ht => heq ht)
    exact absurd hend (ne_of_gt (hpos _ ⟨hzpos, hzT.le⟩))

end Poincare.L4.GeodesicComparison
