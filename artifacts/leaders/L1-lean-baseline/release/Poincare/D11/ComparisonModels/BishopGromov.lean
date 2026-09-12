/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — Bishop–Gromov volume comparison at the ODE level

The volume of the geodesic ball of radius `r` in the `n`-dimensional model space of constant
sectional curvature `K` is `ω_{n-1} · V_K(r)` with

`V_K(r) = ∫₀^r j_K(t)^(n-1) dt`,

where `j_K = Poincare.D10.jacobiSol K` is the D10 normalised Jacobi field.  The sphere factor
`ω_{n-1}` cancels in every ratio, so this file works with the unnormalised `ballVolume n K r`.

**Bishop–Gromov, at the ODE level.**  For `K₂ ≤ K₁` the ratio

`r ↦ V_{K₁}(r) / V_{K₂}(r)`

is monotone non-increasing on every interval `[r₁, r₂]` with `0 < r₁ ≤ r₂` not passing the
first zero `π / √K₁` of `j_{K₁}` (no restriction when `K₁ ≤ 0`).

The proof is a real-analytic monotonicity statement obtained by **derivative sign
computation**, in four steps:

1. **Wronskian.**  `W = j₁'·j₂ - j₁·j₂'` satisfies `W' = (K₂ - K₁)·j₁·j₂ ≤ 0` and `W 0 = 0`
   (the ODE `j'' + K·j = 0` proved in D10 is the only input), hence `W ≤ 0`
   (`wronskian_le_zero`, via `antitoneOn_of_deriv_nonpos`).
2. **Ratio monotonicity.**  `(j₁/j₂)' = W/j₂² ≤ 0`, hence `j₁/j₂` is antitone
   (`jacobiSol_div_antitoneOn`), and in cross-multiplied form
   `j₁(t)·j₂(r) ≤ j₁(t)·j₂(r)` is replaced by `j₁(t)·j₂(r) ≥ j₁(r)·j₂(t)` for `t ≤ r`
   (`jacobiSol_mul_le_mul_of_le`).
3. **Integral estimate.**  Raising to the `(n-1)`-th power (monotone on `[0,∞)`) and
   integrating over `[0, r]` gives `j₁(r)^(n-1)·V₂(r) ≤ V₁(r)·j₂(r)^(n-1)`
   (`ballVolume_ge_jacobiSol_pow`).
4. **Derivative sign of the ratio.**  By the fundamental theorem of calculus
   `V_K'(r) = j_K(r)^(n-1)`, so

   `(V₁/V₂)' = (j₁^(n-1)·V₂ - V₁·j₂^(n-1)) / V₂² ≤ 0`

   (`ballVolume_ratio_deriv_nonpos`), and `antitoneOn_of_deriv_nonpos` on the closed convex
   interval `[r₁, r₂]` yields the two-point Bishop–Gromov statement, including the endpoint
   `r₂ = π/√K₁` (the case where the ball is the whole sphere).

Everything is unconditional: the only comparison input is the D10 ODE verification.
-/
import Poincare.D11.ComparisonModels.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

namespace Poincare.D11

open Set Filter

/-- The unnormalised volume of the geodesic ball of radius `r` in the `n`-dimensional model
space of constant curvature `K`: `∫₀^r j_K(t)^(n-1) dt` (the sphere-factor `ω_{n-1}` is
dropped; it cancels in every comparison). -/
def ballVolume (n : ℕ) (K r : ℝ) : ℝ :=
  ∫ t in 0..r, Poincare.D10.jacobiSol K t ^ (n - 1)

/-- The Wronskian of the two normalised Jacobi fields:
`W(t) = j_{K₁}'(t)·j_{K₂}(t) - j_{K₁}(t)·j_{K₂}'(t)`. -/
def wronskian (K₁ K₂ : ℝ) : ℝ → ℝ :=
  fun t => Poincare.D10.jacobiDeriv K₁ t * Poincare.D10.jacobiSol K₂ t -
    Poincare.D10.jacobiSol K₁ t * Poincare.D10.jacobiDeriv K₂ t

/-- The Wronskian is continuous (each normalised Jacobi field is smooth). -/
theorem continuous_wronskian (K₁ K₂ : ℝ) : Continuous (wronskian K₁ K₂) := by
  unfold wronskian
  exact ((continuous_jacobiDeriv K₁).mul (Poincare.D10.continuous_jacobiSol K₂)).sub
    ((Poincare.D10.continuous_jacobiSol K₁).mul (continuous_jacobiDeriv K₂))

/-- The Wronskian is differentiable. -/
theorem differentiable_wronskian (K₁ K₂ : ℝ) : Differentiable ℝ (wronskian K₁ K₂) := by
  unfold wronskian
  intro t
  exact ((differentiable_jacobiDeriv K₁ t).mul (Poincare.D10.differentiable_jacobiSol K₂ t)).sub
    ((Poincare.D10.differentiable_jacobiSol K₁ t).mul (differentiable_jacobiDeriv K₂ t))

/-- **The Wronskian identity.**  By the Jacobi ODE of D10, the derivative of the Wronskian is
`(K₂ - K₁)·j_{K₁}·j_{K₂}`. -/
theorem wronskian_deriv (K₁ K₂ t : ℝ) :
    deriv (wronskian K₁ K₂) t =
      (K₂ - K₁) * Poincare.D10.jacobiSol K₁ t * Poincare.D10.jacobiSol K₂ t := by
  unfold wronskian
  change deriv ((fun s : ℝ => Poincare.D10.jacobiDeriv K₁ s * Poincare.D10.jacobiSol K₂ s) -
      (fun s : ℝ => Poincare.D10.jacobiSol K₁ s * Poincare.D10.jacobiDeriv K₂ s)) t =
    (K₂ - K₁) * Poincare.D10.jacobiSol K₁ t * Poincare.D10.jacobiSol K₂ t
  rw [deriv_sub]
  · change deriv ((fun s : ℝ => Poincare.D10.jacobiDeriv K₁ s) * (fun s : ℝ => Poincare.D10.jacobiSol K₂ s)) t -
      deriv ((fun s : ℝ => Poincare.D10.jacobiSol K₁ s) * (fun s : ℝ => Poincare.D10.jacobiDeriv K₂ s)) t =
      (K₂ - K₁) * Poincare.D10.jacobiSol K₁ t * Poincare.D10.jacobiSol K₂ t
    rw [deriv_mul (differentiable_jacobiDeriv K₁ t) (Poincare.D10.differentiable_jacobiSol K₂ t),
      deriv_mul (Poincare.D10.differentiable_jacobiSol K₁ t) (differentiable_jacobiDeriv K₂ t)]
    rw [(Poincare.D10.hasDerivAt_jacobiDeriv K₁ t).deriv,
      Poincare.D10.jacobiSol_deriv K₂ t, Poincare.D10.jacobiSol_deriv K₁ t,
      (Poincare.D10.hasDerivAt_jacobiDeriv K₂ t).deriv]
    ring
  · exact (differentiable_jacobiDeriv K₁ t).mul (Poincare.D10.differentiable_jacobiSol K₂ t)
  · exact (Poincare.D10.differentiable_jacobiSol K₁ t).mul (differentiable_jacobiDeriv K₂ t)

/-- **Wronskian sign.**  For `K₂ ≤ K₁`, on `[0, t]` before the first zero of `j_{K₁}` (if
`K₁ > 0`), the Wronskian is nonpositive: `W' = (K₂ - K₁)·j₁·j₂ ≤ 0` with `W 0 = 0`, proved
via `antitoneOn_of_deriv_nonpos`. -/
theorem wronskian_le_zero {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {t : ℝ} (ht : 0 ≤ t)
    (hdom : 0 < K₁ → t ≤ Real.pi / Real.sqrt K₁) : wronskian K₁ K₂ t ≤ 0 := by
  have hanti : AntitoneOn (wronskian K₁ K₂) (Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
    · exact (continuous_wronskian K₁ K₂).continuousOn
    · rw [interior_Icc]
      exact (differentiable_wronskian K₁ K₂).differentiableOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := hx.1.le
      have hxt : x ≤ t := hx.2.le
      rw [wronskian_deriv]
      have hK' : K₂ - K₁ ≤ 0 := sub_nonpos.mpr hK
      have hj1 : 0 ≤ Poincare.D10.jacobiSol K₁ x :=
        Poincare.D10.jacobiSol_nonneg hx0 (fun hK₁ => le_trans hxt (hdom hK₁))
      have hj2 : 0 ≤ Poincare.D10.jacobiSol K₂ x :=
        jacobiSol_nonneg_of_le hK hx0 (fun hK₁ => le_trans hxt (hdom hK₁))
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hK' hj1) hj2
  have h := hanti (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  simpa [wronskian, Poincare.D10.jacobiSol_zero, Poincare.D10.jacobiDeriv_zero] using h

/-- **Ratio monotonicity (Sturm).**  For `K₂ ≤ K₁` the ratio `t ↦ j_{K₁} t / j_{K₂} t` is
antitone on `(0, r₀)`, where `r₀` is any radius not past the first zero of `j_{K₁}`.  The
derivative is `W / j₂² ≤ 0` by `wronskian_le_zero` and the strict positivity of `j₂`. -/
theorem jacobiSol_div_antitoneOn {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r₀ : ℝ}
    (hdom : 0 < K₁ → r₀ ≤ Real.pi / Real.sqrt K₁) :
    AntitoneOn (fun t : ℝ => Poincare.D10.jacobiSol K₁ t / Poincare.D10.jacobiSol K₂ t)
      (Ioo 0 r₀) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 r₀) ?_ ?_ ?_
  · refine (Poincare.D10.continuous_jacobiSol K₁).continuousOn.div
      (Poincare.D10.continuous_jacobiSol K₂).continuousOn ?_
    intro x hx
    exact ne_of_gt (jacobiSol_pos_of_le hK hx.1 (fun hK₁ => lt_of_lt_of_le hx.2 (hdom hK₁)))
  · rw [interior_Ioo]
    refine (Poincare.D10.differentiable_jacobiSol K₁).differentiableOn.div
      (Poincare.D10.differentiable_jacobiSol K₂).differentiableOn ?_
    intro x hx
    exact ne_of_gt (jacobiSol_pos_of_le hK hx.1 (fun hK₁ => lt_of_lt_of_le hx.2 (hdom hK₁)))
  · intro x hx
    rw [interior_Ioo] at hx
    have hderiv : deriv (fun t : ℝ => Poincare.D10.jacobiSol K₁ t / Poincare.D10.jacobiSol K₂ t) x
        = wronskian K₁ K₂ x / Poincare.D10.jacobiSol K₂ x ^ 2 := by
      change deriv (Poincare.D10.jacobiSol K₁ / Poincare.D10.jacobiSol K₂) x
        = wronskian K₁ K₂ x / Poincare.D10.jacobiSol K₂ x ^ 2
      have hj2x : Poincare.D10.jacobiSol K₂ x ≠ 0 := ne_of_gt
        (jacobiSol_pos_of_le hK hx.1 (fun hK₁ => lt_of_lt_of_le hx.2 (hdom hK₁)))
      rw [deriv_div (Poincare.D10.differentiable_jacobiSol K₁ x)
        (Poincare.D10.differentiable_jacobiSol K₂ x) hj2x]
      rw [Poincare.D10.jacobiSol_deriv, Poincare.D10.jacobiSol_deriv]
      unfold wronskian
      rfl
    rw [hderiv]
    have hW : wronskian K₁ K₂ x ≤ 0 :=
      wronskian_le_zero hK hx.1.le (fun hK₁ => le_trans hx.2.le (hdom hK₁))
    exact div_nonpos_of_nonpos_of_nonneg hW (sq_nonneg (Poincare.D10.jacobiSol K₂ x))

/-- **Cross-multiplied ratio monotonicity.**  For `K₂ ≤ K₁`, `0 ≤ t ≤ r` with `r` not past
the first zero of `j_{K₁}`:

`j_{K₁}(r)·j_{K₂}(t) ≤ j_{K₁}(t)·j_{K₂}(r)`.

This is the antitone ratio `j₁/j₂` written without denominators, so it also holds at the
endpoints `t = 0` (both sides `0`) and `r = π/√K₁` (the left-hand side vanishes). -/
theorem jacobiSol_mul_le_mul_of_le {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {t r : ℝ} (ht : 0 ≤ t)
    (htr : t ≤ r) (hdom : 0 < K₁ → r ≤ Real.pi / Real.sqrt K₁) :
    Poincare.D10.jacobiSol K₁ r * Poincare.D10.jacobiSol K₂ t ≤
      Poincare.D10.jacobiSol K₁ t * Poincare.D10.jacobiSol K₂ r := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [Poincare.D10.jacobiSol_zero]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let r₀ := if 0 < K₁ then Real.pi / Real.sqrt K₁ else r + 1
    have hr₀pos : 0 < r₀ := by
      by_cases hK₁ : 0 < K₁
      · simp [r₀, hK₁, div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK₁)]
      · simp [r₀, hK₁]
        linarith [htpos, htr]
    have hr₀dom : 0 < K₁ → r₀ ≤ Real.pi / Real.sqrt K₁ := by
      intro hK₁
      simp [r₀, hK₁]
    have hanti : AntitoneOn (fun s : ℝ => Poincare.D10.jacobiSol K₁ s / Poincare.D10.jacobiSol K₂ s)
        (Ioo 0 r₀) := jacobiSol_div_antitoneOn hK hr₀dom
    by_cases hrlt : r < r₀
    · have htmem : t ∈ Ioo 0 r₀ := ⟨htpos, lt_of_le_of_lt htr hrlt⟩
      have hrpos : 0 < r := lt_of_lt_of_le htpos htr
      have hrmem : r ∈ Ioo 0 r₀ := ⟨hrpos, hrlt⟩
      have hq : Poincare.D10.jacobiSol K₁ r / Poincare.D10.jacobiSol K₂ r ≤
          Poincare.D10.jacobiSol K₁ t / Poincare.D10.jacobiSol K₂ t := hanti htmem hrmem htr
      have hj2t : 0 < Poincare.D10.jacobiSol K₂ t := by
        refine jacobiSol_pos_of_le hK htpos ?_
        intro hK₁
        have hr₀sp : r₀ = Real.pi / Real.sqrt K₁ := by simp [r₀, hK₁]
        exact lt_of_lt_of_le htmem.2 (le_of_eq hr₀sp)
      have hj2r : 0 < Poincare.D10.jacobiSol K₂ r := by
        refine jacobiSol_pos_of_le hK hrpos ?_
        intro hK₁
        have hr₀sp : r₀ = Real.pi / Real.sqrt K₁ := by simp [r₀, hK₁]
        exact lt_of_lt_of_le hrlt (le_of_eq hr₀sp)
      rwa [div_le_div_iff₀ hj2r hj2t] at hq
    · have hreq : r = r₀ := by
        have hle₀ : r ≤ r₀ := by
          by_cases hK₁ : 0 < K₁
          · simp [r₀, hK₁, hdom hK₁]
          · simp [r₀, hK₁]
        exact le_antisymm hle₀ (le_of_not_gt hrlt)
      by_cases hK₁ : 0 < K₁
      · have hj1r : Poincare.D10.jacobiSol K₁ r = 0 := by
          rw [hreq]
          simpa [r₀, hK₁] using Poincare.D10.jacobiSol_firstZero hK₁
        rw [hj1r, zero_mul]
        have hj1t : 0 ≤ Poincare.D10.jacobiSol K₁ t :=
          Poincare.D10.jacobiSol_nonneg ht (fun _ => le_trans htr (hdom hK₁))
        have hj2r : 0 ≤ Poincare.D10.jacobiSol K₂ r :=
          jacobiSol_nonneg_of_le hK (le_trans ht htr) (fun _ => hdom hK₁)
        exact mul_nonneg hj1t hj2r
      · have hr₀eq : r₀ = r + 1 := by simp [r₀, hK₁]
        rw [hr₀eq] at hreq
        linarith

/-- **Integral estimate.**  For `K₂ ≤ K₁` and `0 ≤ r` not past the first zero of `j_{K₁}`:

`j_{K₁}(r)^(n-1) · V_{K₂}(r) ≤ V_{K₁}(r) · j_{K₂}(r)^(n-1)`.

Proof: the cross-multiplied ratio monotonicity is raised to the `(n-1)`-th power (monotone on
`[0, ∞)`) and integrated over `[0, r]`. -/
theorem ballVolume_ge_jacobiSol_pow {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r : ℝ} (hr : 0 ≤ r)
    (hdom : 0 < K₁ → r ≤ Real.pi / Real.sqrt K₁) :
    Poincare.D10.jacobiSol K₁ r ^ (n - 1) * ballVolume n K₂ r ≤
      ballVolume n K₁ r * Poincare.D10.jacobiSol K₂ r ^ (n - 1) := by
  have hpoint : ∀ t ∈ Icc 0 r,
      Poincare.D10.jacobiSol K₁ r ^ (n - 1) * Poincare.D10.jacobiSol K₂ t ^ (n - 1) ≤
        Poincare.D10.jacobiSol K₁ t ^ (n - 1) * Poincare.D10.jacobiSol K₂ r ^ (n - 1) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have htr : t ≤ r := ht.2
    have hmul : Poincare.D10.jacobiSol K₁ r * Poincare.D10.jacobiSol K₂ t ≤
        Poincare.D10.jacobiSol K₁ t * Poincare.D10.jacobiSol K₂ r :=
      jacobiSol_mul_le_mul_of_le hK ht0 htr hdom
    have hnonneg : 0 ≤ Poincare.D10.jacobiSol K₁ r * Poincare.D10.jacobiSol K₂ t := mul_nonneg
      (Poincare.D10.jacobiSol_nonneg hr hdom)
      (jacobiSol_nonneg_of_le hK ht0 (fun hK₁ => le_trans htr (hdom hK₁)))
    have hpow : (Poincare.D10.jacobiSol K₁ r * Poincare.D10.jacobiSol K₂ t) ^ (n - 1) ≤
        (Poincare.D10.jacobiSol K₁ t * Poincare.D10.jacobiSol K₂ r) ^ (n - 1) :=
      pow_le_pow_left₀ hnonneg hmul (n - 1)
    rwa [mul_pow, mul_pow] at hpow
  have hint :
      (∫ t in 0..r, Poincare.D10.jacobiSol K₁ r ^ (n - 1) * Poincare.D10.jacobiSol K₂ t ^ (n - 1)) ≤
        (∫ t in 0..r, Poincare.D10.jacobiSol K₁ t ^ (n - 1) * Poincare.D10.jacobiSol K₂ r ^ (n - 1)) := by
    refine intervalIntegral.integral_mono_on hr ?_ ?_ hpoint
    · exact (continuous_const.mul (continuous_jacobiSol_pow (n - 1) K₂)).intervalIntegrable 0 r
    · exact ((continuous_jacobiSol_pow (n - 1) K₁).mul continuous_const).intervalIntegrable 0 r
  have hc1 :
      (∫ t in 0..r, Poincare.D10.jacobiSol K₁ r ^ (n - 1) * Poincare.D10.jacobiSol K₂ t ^ (n - 1)) =
        Poincare.D10.jacobiSol K₁ r ^ (n - 1) * (∫ t in 0..r, Poincare.D10.jacobiSol K₂ t ^ (n - 1)) := by
    rw [intervalIntegral.integral_const_mul]
  have hc2 :
      (∫ t in 0..r, Poincare.D10.jacobiSol K₁ t ^ (n - 1) * Poincare.D10.jacobiSol K₂ r ^ (n - 1)) =
        (∫ t in 0..r, Poincare.D10.jacobiSol K₁ t ^ (n - 1)) * Poincare.D10.jacobiSol K₂ r ^ (n - 1) := by
    rw [intervalIntegral.integral_mul_const]
  rw [hc1, hc2] at hint
  simpa [ballVolume] using hint

/-- The model ball of positive radius (not past the first zero) has positive volume: the
integrand `j_K(t)^(n-1)` is strictly positive on `(0, r)`. -/
theorem ballVolume_pos {n : ℕ} {K r : ℝ} (hr : 0 < r) (hdom : 0 < K → r ≤ Real.pi / Real.sqrt K) :
    0 < ballVolume n K r := by
  unfold ballVolume
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hr
  · exact (continuous_jacobiSol_pow (n - 1) K).intervalIntegrable 0 r
  · intro t ht
    exact pow_pos (jacobiSol_pos ht.1 (fun hK => lt_of_lt_of_le ht.2 (hdom hK))) (n - 1)

/-- Continuity of `r ↦ V_K(r)` on `[a, b]` with `0 ≤ a`: it is the `Ioc`-primitive of the
continuous function `j_K^(n-1)` (whose `∫ 0..r` form agrees on the interval by
`intervalIntegral.integral_of_le`). -/
theorem continuousOn_ballVolume (n : ℕ) (K : ℝ) {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun r : ℝ => ballVolume n K r) (Icc a b) := by
  have hP : ContinuousOn (fun x : ℝ => ∫ t in Ioc 0 x, (Poincare.D10.jacobiSol K t ^ (n - 1) : ℝ))
      (Icc 0 b) :=
    intervalIntegral.continuousOn_primitive
      ((continuous_jacobiSol_pow (n - 1) K).continuousOn.integrableOn_Icc)
  refine (hP.mono (Icc_subset_Icc_left ha)).congr ?_
  intro x hx
  unfold ballVolume
  exact intervalIntegral.integral_of_le (le_trans ha hx.1)

/-- Differentiability of `r ↦ V_K(r)` on `(a, b)`: the fundamental theorem of calculus gives
`V_K'(r) = j_K(r)^(n-1)`. -/
theorem differentiableOn_ballVolume (n : ℕ) (K : ℝ) (a b : ℝ) :
    DifferentiableOn ℝ (fun r : ℝ => ballVolume n K r) (Ioo a b) := by
  intro x _
  exact (intervalIntegral.integral_hasDerivAt_right
    (f := fun t : ℝ => Poincare.D10.jacobiSol K t ^ (n - 1)) (a := 0) (b := x)
    ((continuous_jacobiSol_pow (n - 1) K).intervalIntegrable 0 x)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
      (fun y _ => (continuous_jacobiSol_pow (n - 1) K).continuousAt) x (mem_univ x))
    ((continuous_jacobiSol_pow (n - 1) K).continuousAt)).differentiableAt.differentiableWithinAt

/-- **Derivative sign computation.**  For `K₂ ≤ K₁`, on `(0, r₀)` (with `r₀` not past the
first zero of `j_{K₁}`) the Bishop–Gromov ratio has nonpositive derivative:

`(V₁/V₂)' = (j₁^(n-1)·V₂ - V₁·j₂^(n-1)) / V₂² ≤ 0`,

where the numerator is nonpositive by the integral estimate
`ballVolume_ge_jacobiSol_pow` and `V₂ > 0`. -/
theorem ballVolume_ratio_deriv_nonpos {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r₀ r : ℝ}
    (hdom₀ : 0 < K₁ → r₀ ≤ Real.pi / Real.sqrt K₁) (hr : r ∈ Ioo 0 r₀) :
    deriv (fun r : ℝ => ballVolume n K₁ r / ballVolume n K₂ r) r ≤ 0 := by
  have hrpos : 0 < r := hr.1
  have hdomr : 0 < K₁ → r ≤ Real.pi / Real.sqrt K₁ := fun hK₁ => le_trans hr.2.le (hdom₀ hK₁)
  have hV2pos : 0 < ballVolume n K₂ r := ballVolume_pos hrpos (fun hK₂ =>
    le_trans (le_trans hr.2.le (hdom₀ (lt_of_lt_of_le hK₂ hK))) (firstZero_le_firstZero hK (lt_of_lt_of_le hK₂ hK) hK₂))
  have hhas (K : ℝ) : HasDerivAt (fun r : ℝ => ballVolume n K r)
      (Poincare.D10.jacobiSol K r ^ (n - 1)) r := by
    unfold ballVolume
    exact intervalIntegral.integral_hasDerivAt_right
      (f := fun t : ℝ => Poincare.D10.jacobiSol K t ^ (n - 1)) (a := 0) (b := r)
      ((continuous_jacobiSol_pow (n - 1) K).intervalIntegrable 0 r)
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
        (fun x _ => (continuous_jacobiSol_pow (n - 1) K).continuousAt) r (mem_univ r))
      ((continuous_jacobiSol_pow (n - 1) K).continuousAt)
  have hd1 (K : ℝ) : deriv (fun r : ℝ => ballVolume n K r) r =
      Poincare.D10.jacobiSol K r ^ (n - 1) := (hhas K).deriv
  have hdiff (K : ℝ) : DifferentiableAt ℝ (fun r : ℝ => ballVolume n K r) r :=
    (hhas K).differentiableAt
  have hd : deriv (fun r : ℝ => ballVolume n K₁ r / ballVolume n K₂ r) r =
      (Poincare.D10.jacobiSol K₁ r ^ (n - 1) * ballVolume n K₂ r -
        ballVolume n K₁ r * Poincare.D10.jacobiSol K₂ r ^ (n - 1)) / ballVolume n K₂ r ^ 2 := by
    change deriv ((fun r : ℝ => ballVolume n K₁ r) / (fun r : ℝ => ballVolume n K₂ r)) r =
      (Poincare.D10.jacobiSol K₁ r ^ (n - 1) * ballVolume n K₂ r -
        ballVolume n K₁ r * Poincare.D10.jacobiSol K₂ r ^ (n - 1)) / ballVolume n K₂ r ^ 2
    rw [deriv_div (hdiff K₁) (hdiff K₂) (ne_of_gt hV2pos), hd1 K₁, hd1 K₂]
  rw [hd]
  have hnum : Poincare.D10.jacobiSol K₁ r ^ (n - 1) * ballVolume n K₂ r -
      ballVolume n K₁ r * Poincare.D10.jacobiSol K₂ r ^ (n - 1) ≤ 0 :=
    sub_nonpos.mpr (ballVolume_ge_jacobiSol_pow hK hrpos.le hdomr)
  exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg (ballVolume n K₂ r))

/-- The Bishop–Gromov ratio is antitone on `(0, r₀)` (with `r₀` not past the first zero of
`j_{K₁}`): the derivative sign computation above is fed to `antitoneOn_of_deriv_nonpos`. -/
theorem ballVolume_ratio_antitoneOn {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r₀ : ℝ}
    (hdom : 0 < K₁ → r₀ ≤ Real.pi / Real.sqrt K₁) :
    AntitoneOn (fun r : ℝ => ballVolume n K₁ r / ballVolume n K₂ r) (Ioo 0 r₀) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 r₀) ?_ ?_ ?_
  · refine ((continuousOn_ballVolume n K₁ (a := 0) (b := r₀) (le_rfl : (0 : ℝ) ≤ 0)).mono
      Ioo_subset_Icc_self).div
      ((continuousOn_ballVolume n K₂ (a := 0) (b := r₀) (le_rfl : (0 : ℝ) ≤ 0)).mono
      Ioo_subset_Icc_self) ?_
    intro x hx
    exact ne_of_gt (ballVolume_pos hx.1 (fun hK₂ =>
      le_trans (le_trans hx.2.le (hdom (lt_of_lt_of_le hK₂ hK))) (firstZero_le_firstZero hK (lt_of_lt_of_le hK₂ hK) hK₂)))
  · rw [interior_Ioo]
    refine (differentiableOn_ballVolume n K₁ 0 r₀).div
      (differentiableOn_ballVolume n K₂ 0 r₀) ?_
    intro x hx
    exact ne_of_gt (ballVolume_pos hx.1 (fun hK₂ =>
      le_trans (le_trans hx.2.le (hdom (lt_of_lt_of_le hK₂ hK))) (firstZero_le_firstZero hK (lt_of_lt_of_le hK₂ hK) hK₂)))
  · intro x hx
    rw [interior_Ioo] at hx
    exact ballVolume_ratio_deriv_nonpos hK hdom hx

/-- **Bishop–Gromov volume comparison at the ODE level.**  If `K₂ ≤ K₁` then for
`0 < r₁ ≤ r₂`, with `r₂` not past the first zero `π/√K₁` of `j_{K₁}` (no restriction when
`K₁ ≤ 0`), the ratio of model ball volumes is monotone non-increasing:

`V_{K₁}(r₂) / V_{K₂}(r₂) ≤ V_{K₁}(r₁) / V_{K₂}(r₁)`.

Proved by the derivative sign computation on the closed convex interval `[r₁, r₂]`
(`antitoneOn_of_deriv_nonpos`), so the endpoint `r₂ = π/√K₁` — where the ball is the whole
spherical space form — is included. -/
theorem bishopGromov_volume_comparison {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hdom : 0 < K₁ → r₂ ≤ Real.pi / Real.sqrt K₁) :
    ballVolume n K₁ r₂ / ballVolume n K₂ r₂ ≤ ballVolume n K₁ r₁ / ballVolume n K₂ r₁ := by
  have hanti : AntitoneOn (fun r : ℝ => ballVolume n K₁ r / ballVolume n K₂ r) (Icc r₁ r₂) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc r₁ r₂) ?_ ?_ ?_
    · refine (continuousOn_ballVolume n K₁ (le_of_lt hr₁)).div
        (continuousOn_ballVolume n K₂ (le_of_lt hr₁)) ?_
      intro x hx
      exact ne_of_gt (ballVolume_pos (lt_of_lt_of_le hr₁ hx.1) (fun hK₂ =>
        le_trans (le_trans hx.2 (hdom (lt_of_lt_of_le hK₂ hK))) (firstZero_le_firstZero hK (lt_of_lt_of_le hK₂ hK) hK₂)))
    · rw [interior_Icc]
      refine (differentiableOn_ballVolume n K₁ r₁ r₂).div
        (differentiableOn_ballVolume n K₂ r₁ r₂) ?_
      intro x hx
      exact ne_of_gt (ballVolume_pos (lt_trans hr₁ hx.1) (fun hK₂ =>
        le_trans (le_trans hx.2.le (hdom (lt_of_lt_of_le hK₂ hK))) (firstZero_le_firstZero hK (lt_of_lt_of_le hK₂ hK) hK₂)))
    · intro x hx
      rw [interior_Icc] at hx
      have hxmem : x ∈ Ioo 0 r₂ := ⟨lt_trans hr₁ hx.1, hx.2⟩
      exact ballVolume_ratio_deriv_nonpos hK hdom hxmem
  exact hanti (left_mem_Icc.mpr hr₁₂) (right_mem_Icc.mpr hr₁₂) hr₁₂

/-- Bishop–Gromov for a nonpositive larger curvature `K₁ ≤ 0`: no first-zero restriction is
needed, since `j_{K₁}` has no zero. -/
theorem bishopGromov_volume_comparison_of_nonpos {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁)
    (hK₁ : K₁ ≤ 0) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) :
    ballVolume n K₁ r₂ / ballVolume n K₂ r₂ ≤ ballVolume n K₁ r₁ / ballVolume n K₂ r₁ :=
  bishopGromov_volume_comparison hK hr₁ hr₁₂ fun h => absurd h (not_lt.mpr hK₁)

/-- Bishop–Gromov for a spherical larger curvature `K₁ > 0`, stated with the first zero
`π/√K₁` explicitly. -/
theorem bishopGromov_volume_comparison_sphere {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁)
    (_hK₁ : 0 < K₁) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hr₂ : r₂ ≤ Real.pi / Real.sqrt K₁) :
    ballVolume n K₁ r₂ / ballVolume n K₂ r₂ ≤ ballVolume n K₁ r₁ / ballVolume n K₂ r₁ :=
  bishopGromov_volume_comparison hK hr₁ hr₁₂ fun _ => hr₂

end Poincare.D11
