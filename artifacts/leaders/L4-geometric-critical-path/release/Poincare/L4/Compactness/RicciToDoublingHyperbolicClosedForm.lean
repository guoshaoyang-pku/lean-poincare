/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — the hyperbolic model volume in elementary closed form (all dimensions)

The companion files `RicciToDoubling.lean` and `RicciToDoublingHyperbolic.lean` prove the
Euclidean and hyperbolic Bishop–Gromov volume-ratio bounds at the scalar/model level.  The
hyperbolic statement `hyp_volume_ratio_le_of_ricci_ge` there carries the constant

    V̄ R / V̄ r,      V̄ t = radialVolume (hypModelA d κ) t = ∫₀ᵗ (sinh(κ s)/κ)^d ds,

i.e. the ratio of two *integral* expressions of the model profile.  This file removes that
last non-elementary ingredient: it proves that the model volume is an **explicit elementary
recursive closed form** for every dimension parameter `d`, so the hyperbolic volume-ratio
bound becomes fully evaluated in terms of `sinh` and `cosh`.

Write `J_d(x) = ∫₀ˣ sinh(u)^d du`.  Integration by parts gives the two-step recursion

    J_0(x) = x,    J_1(x) = cosh x − 1,
    J_{d+2}(x) = ( sinh(x)^{d+1} · cosh x − (d+1)·J_d(x) ) / (d+2)      (d ≥ 0),

which is exactly the definition of `sinhPowIntegral` below (the identity is *proved*, not
assumed: `sinhPowIntegral_integral`).  Substituting `u = κ s` gives

    radialVolume (hypModelA d κ) s = (κ⁻¹)^{d+1} · J_d(κ s)                (`κ ≠ 0`),

so `V̄ R / V̄ r = J_d(κR) / J_d(κ r)` and the hyperbolic Bishop–Gromov bound reads

    radialVolume A R ≤ (J_d(κR) / J_d(κ r)) · radialVolume A r.

For `d = 1` this recovers `cosh(κs) − 1`; for `d = 2`, `J_2(x) = (sinh x·cosh x − x)/2`, so
the ratio is `(sinh(κR)·cosh(κR) − κR)/(sinh(κr)·cosh(κr) − κr)`
(`hypModel_volumeRatio_d2_closedForm`), a completely elementary expression.

## Classification

Every declaration carries a `**Class:**` line.  All declarations of this file are
`**Class:** model (scalar ODE)`: real functions on an interval and their integrals, with no
manifold, metric space, measure, curvature tensor or geodesic content.  The file consumes the
hyperbolic model module; it does not modify it and does not restate any D12 result.
-/
import Poincare.L4.Compactness.RicciToDoublingHyperbolic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Poincare.L4.Compactness

open Poincare.D12.ComparisonGeodesics

/-! ## 1. The explicit elementary antiderivative of `sinh^d` -/

/-- **Class:** model (scalar ODE).

Explicit elementary antiderivative `J_d` of `sinh^d`, defined by the integration-by-parts
recursion `J_0(x) = x`, `J_1(x) = cosh x − 1`,
`J_{d+2}(x) = (sinh(x)^{d+1}·cosh x − (d+1)·J_d(x))/(d+2)`.  Analytic hypotheses: none
(a definition); for every `d` the recursion unfolds to a finite expression in `sinh`, `cosh`
and the variable. -/
def sinhPowIntegral : ℕ → ℝ → ℝ
  | 0, x => x
  | 1, x => Real.cosh x - 1
  | (d + 2), x =>
      ((Real.sinh x) ^ (d + 1) * Real.cosh x - ((d : ℝ) + 1) * sinhPowIntegral d x) /
        ((d : ℝ) + 2)
termination_by d _ => d
decreasing_by omega

/-- **Class:** model (scalar ODE).

Defining equation `J_0(x) = x`.  Analytic hypotheses: none. -/
theorem sinhPowIntegral_zero (x : ℝ) : sinhPowIntegral 0 x = x := by
  simp [sinhPowIntegral]

/-- **Class:** model (scalar ODE).

Defining equation `J_1(x) = cosh x − 1`.  Analytic hypotheses: none. -/
theorem sinhPowIntegral_one (x : ℝ) : sinhPowIntegral 1 x = Real.cosh x - 1 := by
  simp [sinhPowIntegral]

/-- **Class:** model (scalar ODE).

Defining recursion `J_{d+2}(x) = (sinh(x)^{d+1}·cosh x − (d+1)·J_d(x))/(d+2)` for every
`d : ℕ`.  Analytic hypotheses: none. -/
theorem sinhPowIntegral_add_two (d : ℕ) (x : ℝ) :
    sinhPowIntegral (d + 2) x =
      ((Real.sinh x) ^ (d + 1) * Real.cosh x - ((d : ℝ) + 1) * sinhPowIntegral d x) /
        ((d : ℝ) + 2) := by
  rw [sinhPowIntegral.eq_3]

/-- **Class:** model (scalar ODE).

`J_d(0) = 0` for every `d` (all uses of the closed form below are anchored at `0`).
Analytic hypotheses: none. -/
theorem sinhPowIntegral_apply_zero (d : ℕ) : sinhPowIntegral d 0 = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · rw [sinhPowIntegral_zero]
    · rw [sinhPowIntegral_one, Real.cosh_zero]; norm_num
    · rw [sinhPowIntegral_add_two, Real.sinh_zero, ih d (by omega)]
      simp

/-- **Class:** model (scalar ODE).

**The closed form is the antiderivative:** `J_d'(x) = sinh(x)^d`.  Analytic hypotheses: none
(the statement holds for every real `x` and every `d`). -/
theorem sinhPowIntegral_hasDerivAt (d : ℕ) (x : ℝ) :
    HasDerivAtR (fun y => sinhPowIntegral d y) (Real.sinh x ^ d) x := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · have h : HasDerivAtR (fun y : ℝ => y) 1 x := hasDerivAtR_id x
      convert h using 1
      · ext y; rw [sinhPowIntegral_zero]
      · rw [pow_zero]
    · have h : HasDerivAtR (fun y : ℝ => Real.cosh y - 1) (Real.sinh x) x :=
        (Real.hasDerivAt_cosh x).sub_const 1
      convert h using 1
      · ext y; rw [sinhPowIntegral_one]
      · rw [pow_one]
    · have hih : HasDerivAtR (fun y => sinhPowIntegral d y) (Real.sinh x ^ d) x :=
        ih d (by omega)
      have hpow : HasDerivAtR (fun y : ℝ => Real.sinh y ^ (d + 1))
          (((d + 1 : ℕ) : ℝ) * Real.sinh x ^ d * Real.cosh x) x := by
        convert (Real.hasDerivAt_sinh x).pow (d + 1) using 1
        · ext y; rfl
        · rw [Nat.add_sub_cancel]
      have hcosh : HasDerivAtR (fun y : ℝ => Real.cosh y) (Real.sinh x) x :=
        Real.hasDerivAt_cosh x
      have hmul : HasDerivAtR (fun y : ℝ => Real.sinh y ^ (d + 1) * Real.cosh y)
          ((((d + 1 : ℕ) : ℝ) * Real.sinh x ^ d * Real.cosh x) * Real.cosh x
            + Real.sinh x ^ (d + 1) * Real.sinh x) x := by
        have h := hpow.mul hcosh
        convert h using 1
        · ext y; rfl
      have hsub : HasDerivAtR (fun y : ℝ => Real.sinh y ^ (d + 1) * Real.cosh y
            - ((d : ℝ) + 1) * sinhPowIntegral d y)
          ((((d + 1 : ℕ) : ℝ) * Real.sinh x ^ d * Real.cosh x) * Real.cosh x
            + Real.sinh x ^ (d + 1) * Real.sinh x
            - ((d : ℝ) + 1) * Real.sinh x ^ d) x := by
        have h := hmul.sub (hih.const_mul ((d : ℝ) + 1))
        convert h using 1
        · ext y; rfl
      have hdiv : HasDerivAtR (fun y : ℝ => (Real.sinh y ^ (d + 1) * Real.cosh y
            - ((d : ℝ) + 1) * sinhPowIntegral d y) / ((d : ℝ) + 2))
          (((((d + 1 : ℕ) : ℝ) * Real.sinh x ^ d * Real.cosh x) * Real.cosh x
            + Real.sinh x ^ (d + 1) * Real.sinh x
            - ((d : ℝ) + 1) * Real.sinh x ^ d) / ((d : ℝ) + 2)) x :=
        hsub.div_const ((d : ℝ) + 2)
      have hfun : (fun y : ℝ => sinhPowIntegral (d + 2) y) = fun y : ℝ =>
          (Real.sinh y ^ (d + 1) * Real.cosh y - ((d : ℝ) + 1) * sinhPowIntegral d y) /
            ((d : ℝ) + 2) := by
        funext y
        rw [sinhPowIntegral_add_two]
      rw [hfun]
      convert hdiv using 1
      have hcosh2 : Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1 := by
        have h := Real.cosh_sq_sub_sinh_sq x
        linarith
      have hA : Real.sinh x ^ (d + 1) * Real.sinh x = Real.sinh x ^ (d + 2) := by
        rw [← pow_succ]
      have hB : Real.sinh x ^ d * (Real.sinh x ^ 2 + 1)
          = Real.sinh x ^ (d + 2) + Real.sinh x ^ d := by
        rw [mul_add, mul_one, ← pow_add]
      have hd2 : ((d : ℝ) + 2) ≠ 0 := by positivity
      rw [eq_div_iff hd2]
      push_cast
      rw [show (↑d + 1) * Real.sinh x ^ d * Real.cosh x * Real.cosh x
            = (↑d + 1) * (Real.sinh x ^ d * Real.cosh x ^ 2) by ring]
      rw [hcosh2, hA, hB]
      ring

/-- **Class:** model (scalar ODE).

**The integral identity:** `∫₀ˢ sinh(t)^d dt = J_d(s)` for every real `s` and every `d`.
Analytic hypotheses: none. -/
theorem sinhPowIntegral_integral (d : ℕ) (s : ℝ) :
    ∫ t in (0)..s, Real.sinh t ^ d = sinhPowIntegral d s := by
  have hcont : Continuous fun t : ℝ => Real.sinh t ^ d := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := s)
    (f := fun y : ℝ => sinhPowIntegral d y) (f' := fun t : ℝ => Real.sinh t ^ d)
    (fun x _ => sinhPowIntegral_hasDerivAt d x) (hcont.intervalIntegrable _ _)
  rw [h, sinhPowIntegral_apply_zero, sub_zero]

/-! ## 2. Small-dimension evaluations -/

/-- **Class:** model (scalar ODE).

`J_2(x) = (sinh x · cosh x − x)/2` (i.e. `sinh(2x)/4 − x/2`).  Analytic hypotheses: none. -/
theorem sinhPowIntegral_two (x : ℝ) :
    sinhPowIntegral 2 x = (Real.sinh x * Real.cosh x - x) / 2 := by
  rw [sinhPowIntegral_add_two (d := 0) x, sinhPowIntegral_zero]
  norm_num

/-- **Class:** model (scalar ODE).

`J_3(x) = (sinh(x)²·cosh x − 2(cosh x − 1))/3` (i.e. `(cosh(x)³ − 3cosh x + 2)/3`).
Analytic hypotheses: none. -/
theorem sinhPowIntegral_three (x : ℝ) :
    sinhPowIntegral 3 x =
      ((Real.sinh x) ^ 2 * Real.cosh x - 2 * (Real.cosh x - 1)) / 3 := by
  rw [sinhPowIntegral_add_two (d := 1) x, sinhPowIntegral_one]
  norm_num

/-! ## 3. The model volume and volume ratio in closed form -/

/-- **Class:** model (scalar ODE).

**Closed form of the hyperbolic model volume.**  For `κ ≠ 0` and every real `s`,

    radialVolume (hypModelA d κ) s = (κ⁻¹)^{d+1} · J_d(κ·s),

equivalently `∫₀ˢ (sinh(κt)/κ)^d dt = κ^{-(d+1)} J_d(κs)`.  Analytic hypotheses: `κ ≠ 0`
(the substitution `u = κt`); no positivity of `s` is needed.  This turns the integral model
volume into an explicit elementary expression for every `d`.

Proof: the change of variables `u = κt` gives `∫₀ˢ sinh(κt)^d dt = κ⁻¹ J_d(κs)`, and the
constant `κ^{-d}` is pulled out of the integral. -/
theorem hypModelA_volume_closedForm {d : ℕ} {κ : ℝ} (hκ : κ ≠ 0) (s : ℝ) :
    radialVolume (hypModelA d κ) s = (κ⁻¹) ^ (d + 1) * sinhPowIntegral d (κ * s) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := s)
    (f := fun t : ℝ => κ * t) (f' := fun _ => κ) (g := fun u : ℝ => Real.sinh u ^ d)
    (fun x _ => hasDerivAt_const_mul (x := x) κ) continuous_const.continuousOn (by fun_prop)
  rw [mul_zero, sinhPowIntegral_integral] at hsub
  have hInt : ∫ t in (0)..s, Real.sinh (κ * t) ^ d = κ⁻¹ * sinhPowIntegral d (κ * s) := by
    have h1 : (∫ t in (0)..s, Real.sinh (κ * t) ^ d) * κ = sinhPowIntegral d (κ * s) := by
      rw [← intervalIntegral.integral_mul_const]
      exact hsub
    rw [← h1]
    field_simp
  have hpt : ∀ t : ℝ, hypModelA d κ t = (κ⁻¹) ^ d * Real.sinh (κ * t) ^ d := by
    intro t
    unfold hypModelA
    rw [div_eq_mul_inv, mul_pow]
    ring
  unfold radialVolume
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, hInt]
  rw [show (κ⁻¹) ^ d * (κ⁻¹ * sinhPowIntegral d (κ * s))
        = ((κ⁻¹) ^ d * κ⁻¹) * sinhPowIntegral d (κ * s) by ring]
  rw [← pow_succ]

/-- **Class:** model (scalar ODE).

**Closed form of the hyperbolic model volume ratio.**  For `κ ≠ 0`,

    V̄ R / V̄ r = J_d(κR) / J_d(κr),      V̄ t = radialVolume (hypModelA d κ) t,

the `κ^{-(d+1)}` prefactor cancelling.  This is the elementary hyperbolic closed form that
`hyp_volume_ratio_le_of_ricci_ge` leaves as an unevaluated model ratio.  Analytic hypotheses:
`κ ≠ 0` only. -/
theorem hypModel_volumeRatio_closedForm {d : ℕ} {κ r R : ℝ} (hκ : κ ≠ 0) :
    radialVolume (hypModelA d κ) R / radialVolume (hypModelA d κ) r =
      sinhPowIntegral d (κ * R) / sinhPowIntegral d (κ * r) := by
  rw [hypModelA_volume_closedForm (d := d) hκ R, hypModelA_volume_closedForm (d := d) hκ r]
  have hk : (κ⁻¹) ^ (d + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hκ)
  field_simp

/-- **Class:** model (scalar ODE).

Dimension-one consistency with the existing evaluated form: `radialVolume (hypModelA 1 1) s`
is `cosh s − 1`, matching `hypModelA_one_one_volume` of the companion module but derived here
through the closed form.  Analytic hypotheses: none. -/
theorem hypModelA_one_one_volume_closedForm (s : ℝ) :
    radialVolume (hypModelA 1 1) s = Real.cosh s - 1 := by
  rw [hypModelA_volume_closedForm (by norm_num : (1 : ℝ) ≠ 0)]
  norm_num [sinhPowIntegral_one]

/-- **Class:** model (scalar ODE).

Dimension-two hyperbolic volume ratio, fully elementary:

    V̄ R / V̄ r = (sinh(κR)·cosh(κR) − κR) / (sinh(κr)·cosh(κr) − κr).

Analytic hypotheses: `κ ≠ 0`.  This is `hypModel_volumeRatio_closedForm` at `d = 2` with
`sinhPowIntegral_two`. -/
theorem hypModel_volumeRatio_d2_closedForm {κ r R : ℝ} (hκ : κ ≠ 0) :
    radialVolume (hypModelA 2 κ) R / radialVolume (hypModelA 2 κ) r =
      (Real.sinh (κ * R) * Real.cosh (κ * R) - κ * R) /
        (Real.sinh (κ * r) * Real.cosh (κ * r) - κ * r) := by
  rw [hypModel_volumeRatio_closedForm (d := 2) hκ, sinhPowIntegral_two, sinhPowIntegral_two]
  rw [div_div_div_cancel_right₀ (show (2 : ℝ) ≠ 0 by norm_num)]

/-! ## 4. The closed-form Bishop–Gromov bound and its doubling consequence -/

/-- **Class:** model (scalar ODE).

**Hyperbolic Bishop–Gromov volume bound, closed form.**  Same analytic hypotheses as
`hyp_volume_ratio_le_of_ricci_ge` of the companion module (`0 < d`, `0 < κ`, `0 < T`,
`0 ≤ C`, `0 < t₀ ≤ T`, model-normalization constant `d·κ ≤ C`; radial curvature
`−d·κ² ≤ k t` on `(0,T)`; Riccati inequality `dm t + m t²/d + k t ≤ 0`; `m` differentiable
with derivative `dm`, continuous on `(0,T]`, Euclidean-normalized `|m t − d/t| ≤ C` on
`(0,t₀)`; `A` differentiable on `(0,T)` with derivative `dA`, continuous on `[0,T]`, positive
on `(0,T]`, `A 0 = 0`, `m = dA/A` on `(0,T)`; `0 < r ≤ R ≤ T`).  Conclusion, with the model
volume replaced by its elementary closed form:

    radialVolume A R ≤ (J_d(κR) / J_d(κr)) · radialVolume A r.

Derived from `hyp_volume_ratio_le_of_ricci_ge` by the closed-form ratio; Bishop–Gromov is
proved through D12, not assumed. -/
theorem hyp_volume_ratio_le_of_ricci_ge_closedForm {d : ℕ} (hdpos : 0 < d) {κ T C t₀ : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hdκC : (d : ℝ) * κ ≤ C)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → hypModelK d κ ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {r R : ℝ} (hr : r ∈ Ioc 0 T) (hR : R ∈ Ioc 0 T) (hrR : r ≤ R) :
    radialVolume A R ≤ (sinhPowIntegral d (κ * R) / sinhPowIntegral d (κ * r)) *
      radialVolume A r := by
  have h := hyp_volume_ratio_le_of_ricci_ge (d := d) hdpos hκ hT hC ht₀ ht₀T hdκC
    hk hineq hm hmcont hnorm hA hAcont hApos hA0 hmA hr hR hrR
  rwa [hypModel_volumeRatio_closedForm (d := d) (κ := κ) (r := r) (R := R)
    (ne_of_gt hκ)] at h

/-- **Class:** model (scalar ODE).

**Hyperbolic single-scale doubling, closed form.**  Under the hypotheses of
`hyp_volume_ratio_le_of_ricci_ge_closedForm` and `0 < s`, `s ≤ T`, `2s ≤ T`,

    radialVolume A (2s) ≤ (J_d(2κs) / J_d(κs)) · radialVolume A s.

The constant is explicit and elementary; it is scale-dependent, which is the honest
negative-curvature statement (there is no scale-uniform hyperbolic doubling constant).
Analytic hypotheses are those of `hyp_volume_ratio_le_of_ricci_ge_closedForm` plus
`0 < s`, `s ≤ T`, `2s ≤ T`. -/
theorem hyp_volume_doubling_closedForm {d : ℕ} (hdpos : 0 < d) {κ T C t₀ : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hdκC : (d : ℝ) * κ ≤ C)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → hypModelK d κ ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) (h2s : 2 * s ≤ T) :
    radialVolume A (2 * s) ≤
      (sinhPowIntegral d (2 * (κ * s)) / sinhPowIntegral d (κ * s)) * radialVolume A s := by
  have h := hyp_volume_ratio_le_of_ricci_ge_closedForm (d := d) hdpos hκ hT hC ht₀ ht₀T hdκC
    hk hineq hm hmcont hnorm hA hAcont hApos hA0 hmA ⟨hs, hsT⟩ ⟨by linarith, h2s⟩ (by linarith)
  have h2 : 2 * (κ * s) = κ * (2 * s) := by ring
  rw [← h2] at h
  exact h

end Poincare.L4.Compactness
