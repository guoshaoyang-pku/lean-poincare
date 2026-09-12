import Poincare.D7.Reduced.Statements
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Poincare.D7.Reduced.Gaussian

**D7 reduced length / reduced volume layer, part 4: the finite-dimensional Gaussian shrinking
soliton model.**

The Gaussian shrinking soliton is `(ℝ^n, δ)` with the flat metric and potential
`f(x) = |x|²/4`; it is the model case in which the reduced length can be computed explicitly.
In backward time `τ` the `L`-geodesic from the origin to `q` is
`γ(σ) = (√σ / √τ) • q`, and

```
L(γ) = ∫_0^τ √σ |γ'(σ)|² dσ = |q|² / (2 √τ),
l(q, τ) = L(γ) / (2 √τ) = |q|² / (4 τ).
```

This module instantiates the stated metric-flow interface `MetricFlowInterface` with the
Gaussian model and proves, kernel-checked:

* `gaussianFlow n` — the interface with zero scalar curvature and the Euclidean metric;
* `integral_one_div_sqrt` — `∫_0^τ σ^{-1/2} dσ = 2 √τ`;
* `gaussian_integrand` — the pointwise value of the `L`-length integrand along the geodesic;
* `gaussian_LlengthAlong` — the explicit `L`-length `|q|² / (2 √τ)`;
* `gaussian_reducedLengthAlong` — the explicit reduced length `|q|² / (4 τ)`;
* `gaussianLPath` — the geodesic as an admissible `LPath`;
* `gaussian_length_le` — **minimality**: every admissible competitor has `L`-length at least
  `|q|² / (2 √τ)` (the proof is the completing-the-square inequality
  `√σ |γ' - v|² ≥ 0` integrated over `[0, τ]`);
* `gaussian_isLMinimizer`, `gaussianReducedLengthData` — the packaged minimiser and its reduced
  length;
* `gaussianLMinimizerExistence` — the state-only existence `Prop` of
  `Poincare.D7.Reduced.Statements` is **proved** for the Gaussian model, a non-vacuity witness.

Every proof is complete; there is no `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` in this file.
-/

open MeasureTheory intervalIntegral Set
open scoped RealInnerProductSpace

namespace Poincare
namespace D7
namespace Reduced

noncomputable section

variable {n : ℕ}

/-- **The Gaussian shrinking soliton model** as a metric-flow interface: flat metric and zero
scalar curvature. -/
def gaussianFlow (n : ℕ) : MetricFlowInterface (EuclideanSpace ℝ (Fin n)) where
  scalarCurvature := fun _ _ => 0
  metric := fun _ x y => ⟪x, y⟫
  metric_symm := fun _ x y => (real_inner_comm x y).symm
  metric_self_nonneg := fun _ x => real_inner_self_nonneg (x := x)
  metric_add_left := fun _ x y z => inner_add_left x y z
  metric_smul_left := fun _ c x y => real_inner_smul_left x y c

@[simp] theorem gaussianFlow_scalarCurvature (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (gaussianFlow n).scalarCurvature τ x = 0 := rfl

@[simp] theorem gaussianFlow_metric (τ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    (gaussianFlow n).metric τ x y = ⟪x, y⟫ := rfl

/-- The `L`-geodesic from the origin to `q` at backward time `τ`:
`γ(σ) = (√σ / √τ) • q`. -/
def gaussianPath (q : EuclideanSpace ℝ (Fin n)) (τ : ℝ) : ℝ → EuclideanSpace ℝ (Fin n) :=
  fun σ => (Real.sqrt σ / Real.sqrt τ) • q

/-- The velocity field of the `L`-geodesic: `γ'(σ) = (1 / (2 √τ √σ)) • q`. -/
def gaussianVelocity (q : EuclideanSpace ℝ (Fin n)) (τ : ℝ) : ℝ → EuclideanSpace ℝ (Fin n) :=
  fun σ => (1 / (2 * Real.sqrt τ * Real.sqrt σ)) • q

/-! ## 1. The integral `∫_0^τ σ^{-1/2} dσ = 2 √τ` -/

/-- `∫_0^τ 1 / √σ dσ = 2 √τ` for `τ ≥ 0`.  This is the elementary integral behind the explicit
Gaussian `L`-length computation; it is proved from `integral_rpow` with exponent `-1/2`. -/
theorem integral_one_div_sqrt {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ σ in (0 : ℝ)..τ, 1 / Real.sqrt σ = 2 * Real.sqrt τ := by
  have hrpow : ∫ σ in (0 : ℝ)..τ, σ ^ (-(1 / 2 : ℝ)) =
      (τ ^ ((-(1 / 2 : ℝ)) + 1) - (0 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) / ((-(1 / 2 : ℝ)) + 1) :=
    integral_rpow (a := 0) (b := τ) (r := -(1 / 2 : ℝ)) (Or.inl (by norm_num))
  have hcongr : ∫ σ in (0 : ℝ)..τ, σ ^ (-(1 / 2 : ℝ)) =
      ∫ σ in (0 : ℝ)..τ, 1 / Real.sqrt σ := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have hσ' : σ ∈ Set.Icc (0 : ℝ) τ := by simpa [Set.uIcc_of_le hτ] using hσ
    rw [Real.rpow_neg hσ'.1, ← Real.sqrt_eq_rpow]
    simp [one_div]
  rw [← hcongr, hrpow]
  have hexp : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero, ← Real.sqrt_eq_rpow]
  field_simp

/-! ## 2. The explicit `L`-length and reduced length -/

/-- Pointwise value of the `L`-length integrand along the Gaussian `L`-geodesic:
`√σ |γ'(σ)|² = |q|² / (4 τ √σ)` for positive `σ`. -/
theorem gaussian_integrand (q : EuclideanSpace ℝ (Fin n)) {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) :
    Real.sqrt σ * ⟪gaussianVelocity q τ σ, gaussianVelocity q τ σ⟫ =
      ‖q‖ ^ 2 / (4 * τ * Real.sqrt σ) := by
  have hσne : Real.sqrt σ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hσ)
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  rw [gaussianVelocity, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp [hσne, hτne]
  rw [Real.sq_sqrt hτ.le]
  ring

/-- **Explicit `L`-length of the Gaussian `L`-geodesic**: `L(γ) = |q|² / (2 √τ)`. -/
theorem gaussian_LlengthAlong (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    (gaussianFlow n).LlengthAlong (gaussianPath q τ) (gaussianVelocity q τ) 0 τ =
      ‖q‖ ^ 2 / (2 * Real.sqrt τ) := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  unfold MetricFlowInterface.LlengthAlong MetricFlowInterface.LIntegrandAlong
  simp only [gaussianFlow]
  have hpoint : ∀ σ ∈ Set.uIcc (0 : ℝ) τ,
      Real.sqrt σ * (0 + ⟪gaussianVelocity q τ σ, gaussianVelocity q τ σ⟫) =
        (‖q‖ ^ 2 / (4 * τ)) * (1 / Real.sqrt σ) := by
    intro σ hσmem
    have hσ' : σ ∈ Set.Icc (0 : ℝ) τ := by simpa [Set.uIcc_of_le hτ.le] using hσmem
    rcases eq_or_lt_of_le hσ'.1 with hzero | hpos
    · subst hzero
      simp [gaussianVelocity]
    · rw [zero_add, gaussian_integrand q hτ hpos]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)]
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul,
    integral_one_div_sqrt hτ.le]
  field_simp [hτne]
  rw [Real.sq_sqrt hτ.le]
  ring

/-- **Explicit reduced length of the Gaussian shrinking soliton model**:
`l(q, τ) = L(γ) / (2 √τ) = |q|² / (4 τ)`. -/
theorem gaussian_reducedLengthAlong (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    (gaussianFlow n).reducedLengthAlong (gaussianPath q τ) (gaussianVelocity q τ) τ =
      ‖q‖ ^ 2 / (4 * τ) := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  unfold MetricFlowInterface.reducedLengthAlong
  rw [gaussian_LlengthAlong q hτ]
  field_simp [hτne]
  rw [Real.sq_sqrt hτ.le]
  ring

/-! ## 3. The Gaussian geodesic as an admissible path -/

/-- The `L`-geodesic has the stated velocity at every positive time. -/
theorem gaussianPath_hasDerivAt (q : EuclideanSpace ℝ (Fin n)) {τ σ : ℝ}
    (hσ : 0 < σ) :
    HasDerivAt (gaussianPath q τ) (gaussianVelocity q τ σ) σ := by
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt σ)) σ :=
    Real.hasDerivAt_sqrt (ne_of_gt hσ)
  have hdiv : HasDerivAt (fun s : ℝ => Real.sqrt s / Real.sqrt τ)
      ((1 / (2 * Real.sqrt σ)) / Real.sqrt τ) σ :=
    hsqrt.div_const (Real.sqrt τ)
  have hsmul : HasDerivAt (fun y : ℝ => (Real.sqrt y / Real.sqrt τ) • q)
      (((1 / (2 * Real.sqrt σ)) / Real.sqrt τ) • q) σ := hdiv.smul_const q
  have hvel : gaussianVelocity q τ σ = ((1 / (2 * Real.sqrt σ)) / Real.sqrt τ) • q := by
    simp only [gaussianVelocity]
    congr 1
    ring
  change HasDerivAt (fun y : ℝ => (Real.sqrt y / Real.sqrt τ) • q)
    (gaussianVelocity q τ σ) σ
  rw [hvel]
  exact hsmul

/-- `∫_0^τ 1 / √σ dσ` is interval-integrable. -/
theorem intervalIntegrable_one_div_sqrt {τ : ℝ} (hτ : 0 < τ) :
    IntervalIntegrable (fun σ : ℝ => 1 / Real.sqrt σ) volume 0 τ :=
  (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := τ)
      (r := (-(1 / 2) : ℝ)) (by norm_num)).congr fun σ hσ => by
    have hσ0 : 0 < σ := (uIoc_of_le hτ.le ▸ hσ : σ ∈ Set.Ioc 0 τ).1
    rw [Real.rpow_neg hσ0.le, ← Real.sqrt_eq_rpow]
    simp [one_div]

/-- The Gaussian `L`-geodesic as an admissible path for the minimisation problem. -/
def gaussianLPath (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    LPath (gaussianFlow n) 0 q τ where
  curve := gaussianPath q τ
  velocity := gaussianVelocity q τ
  curve_zero := by
    simp [gaussianPath]
  curve_tau := by
    have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
    simp [gaussianPath, div_self hτne]
  continuous_curve := by
    change ContinuousOn (fun σ : ℝ => (Real.sqrt σ / Real.sqrt τ) • q) (Set.Icc 0 τ)
    exact ContinuousOn.smul
      ((Real.continuous_sqrt.continuousOn).div_const (Real.sqrt τ)) continuousOn_const
  hasDerivAt := fun σ hσ => gaussianPath_hasDerivAt q hσ.1
  integrable_energy := by
    refine ((intervalIntegrable_one_div_sqrt hτ).const_mul (‖q‖ ^ 2 / (4 * τ))).congr
      fun σ hσ => ?_
    have hσ0 : 0 < σ := (uIoc_of_le hτ.le ▸ hσ : σ ∈ Set.Ioc 0 τ).1
    simp only [gaussianFlow_metric]
    rw [gaussian_integrand q hτ hσ0]
    ring
  integrable_cross := fun c => by
    refine ((intervalIntegrable_one_div_sqrt hτ).const_mul (⟪c, q⟫ / (2 * Real.sqrt τ))).congr
      fun σ hσ => ?_
    have hσ0 : 0 < σ := (uIoc_of_le hτ.le ▸ hσ : σ ∈ Set.Ioc 0 τ).1
    simp only [gaussianFlow_metric]
    rw [gaussianVelocity, real_inner_smul_right]
    ring

/-! ## 4. Minimality of the Gaussian `L`-geodesic -/

/-- **Minimality of the Gaussian `L`-geodesic.**  Every admissible path `P` from the origin to
`q` over `[0, τ]` has `L`-length at least `|q|² / (2 √τ)`.

The proof is the completing-the-square identity

```
√σ |γ'(σ)|² - 2 ⟪c, γ'(σ)⟫ + |c|² / √σ = √σ |γ'(σ) - (1/√σ) c|² ≥ 0,
c = q / (2 √τ),
```

integrated over `[0, τ]`; the first two terms integrate to the `L`-length minus
`|q|² / (2 √τ)` by the fundamental theorem of calculus and `∫_0^τ σ^{-1/2} dσ = 2 √τ`. -/
theorem gaussian_length_le (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ)
    (P : LPath (gaussianFlow n) 0 q τ) :
    ‖q‖ ^ 2 / (2 * Real.sqrt τ) ≤ P.length := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  set c : EuclideanSpace ℝ (Fin n) := (1 / (2 * Real.sqrt τ)) • q with hc
  -- (1) The cross term integrates to `⟪c, q⟫` by the fundamental theorem of calculus.
  have hcross : ∫ σ in (0 : ℝ)..τ, ⟪c, P.velocity σ⟫ = ⟪c, q⟫ := by
    have hcont : ContinuousOn (fun σ : ℝ => ⟪c, P.curve σ⟫) (Set.Icc 0 τ) :=
      continuousOn_const.inner P.continuous_curve
    have hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) τ,
        HasDerivAt (fun σ : ℝ => ⟪c, P.curve σ⟫) (⟪c, P.velocity σ⟫) σ := by
      intro σ hσ
      have hconst : HasDerivAt (fun _ : ℝ => c) 0 σ := hasDerivAt_const σ c
      have hinner := HasDerivAt.inner ℝ hconst (P.hasDerivAt σ hσ)
      simpa using hinner
    have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.le hcont hderiv
      (P.integrable_cross c)
    rw [hInt, P.curve_tau, P.curve_zero]
    simp
  -- (2) Integrability of the three pieces of the completing-the-square integrand.
  have hIntEnergy : IntervalIntegrable
      (fun σ : ℝ => Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫) volume 0 τ :=
    P.integrable_energy
  have hIntCross : IntervalIntegrable (fun σ : ℝ => ⟪c, P.velocity σ⟫) volume 0 τ :=
    P.integrable_cross c
  have hIntInv : IntervalIntegrable (fun σ : ℝ => ⟪c, c⟫ / Real.sqrt σ) volume 0 τ := by
    refine ((intervalIntegrable_one_div_sqrt hτ).const_mul ⟪c, c⟫).congr fun σ _ => ?_
    rw [div_eq_mul_inv]
    ring
  -- (3) The integral of the completing-the-square integrand.
  have hInvMul : ∫ σ in (0 : ℝ)..τ, ⟪c, c⟫ / Real.sqrt σ = ⟪c, c⟫ * (2 * Real.sqrt τ) := by
    rw [← integral_one_div_sqrt hτ.le, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [div_eq_mul_inv]
    ring
  have hfint : ∫ σ in (0 : ℝ)..τ,
      (Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ - 2 * ⟪c, P.velocity σ⟫
        + ⟪c, c⟫ / Real.sqrt σ) =
      (∫ σ in (0 : ℝ)..τ, Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫)
        - 2 * (∫ σ in (0 : ℝ)..τ, ⟪c, P.velocity σ⟫)
        + ⟪c, c⟫ * (2 * Real.sqrt τ) := by
    rw [intervalIntegral.integral_add
      (hIntEnergy.sub (hIntCross.const_mul 2)) hIntInv,
      intervalIntegral.integral_sub hIntEnergy (hIntCross.const_mul 2),
      intervalIntegral.integral_const_mul, hInvMul]
  -- (4) The `L`-length of `P` is the energy integral.
  have hlength : P.length = ∫ σ in (0 : ℝ)..τ,
      Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ := by
    simp [LPath.length, MetricFlowInterface.LlengthAlong, MetricFlowInterface.LIntegrandAlong,
      gaussianFlow]
  -- (5) The completing-the-square integrand is nonnegative almost everywhere.
  have hnonneg : ∀ σ ∈ Set.Ioc (0 : ℝ) τ,
      0 ≤ Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ - 2 * ⟪c, P.velocity σ⟫
        + ⟪c, c⟫ / Real.sqrt σ := by
    intro σ hσ
    have hσ0 : 0 < σ := hσ.1
    have hσne : Real.sqrt σ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hσ0)
    have hid : Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ - 2 * ⟪c, P.velocity σ⟫
        + ⟪c, c⟫ / Real.sqrt σ =
        Real.sqrt σ * ⟪P.velocity σ - (1 / Real.sqrt σ) • c,
          P.velocity σ - (1 / Real.sqrt σ) • c⟫ := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_right,
        real_inner_smul_left, real_inner_comm (P.velocity σ) c]
      field_simp [hσne]
      ring
    rw [hid]
    exact mul_nonneg (Real.sqrt_nonneg σ) real_inner_self_nonneg
  have hae : ∀ᵐ σ ∂volume.restrict (Set.Icc (0 : ℝ) τ),
      0 ≤ Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ - 2 * ⟪c, P.velocity σ⟫
        + ⟪c, c⟫ / Real.sqrt σ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ (by simp : volume ({0} : Set ℝ) = 0)
    intro σ hσ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hσ ⊢
    by_contra hσ0
    exact hσ fun hσIcc => hnonneg σ ⟨lt_of_le_of_ne hσIcc.1 (Ne.symm hσ0), hσIcc.2⟩
  -- (6) Combine.
  have hInt : 0 ≤ ∫ σ in (0 : ℝ)..τ,
      (Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ - 2 * ⟪c, P.velocity σ⟫
        + ⟪c, c⟫ / Real.sqrt σ) :=
    intervalIntegral.integral_nonneg_of_ae_restrict hτ.le hae
  have hcq : ⟪c, q⟫ = (1 / (2 * Real.sqrt τ)) * ‖q‖ ^ 2 := by
    rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hcc : ⟪c, c⟫ = (1 / (2 * Real.sqrt τ)) ^ 2 * ‖q‖ ^ 2 := by
    rw [hc, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  rw [hfint, hcross, ← hlength, hcq, hcc] at hInt
  have hgoal : P.length - 2 * ((1 / (2 * Real.sqrt τ)) * ‖q‖ ^ 2)
      + (1 / (2 * Real.sqrt τ)) ^ 2 * ‖q‖ ^ 2 * (2 * Real.sqrt τ)
      = P.length - ‖q‖ ^ 2 / (2 * Real.sqrt τ) := by
    field_simp [hτne]
    ring
  rw [hgoal] at hInt
  linarith

/-- **The Gaussian geodesic is an `L`-length minimiser.** -/
theorem gaussian_isLMinimizer (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    IsLMinimizer (gaussianLPath (n := n) q hτ) := by
  intro Q
  have h := gaussian_length_le q hτ Q
  have hpath : (gaussianLPath (n := n) q hτ).length = ‖q‖ ^ 2 / (2 * Real.sqrt τ) := by
    show (gaussianFlow n).LlengthAlong (gaussianPath q τ) (gaussianVelocity q τ) 0 τ = _
    exact gaussian_LlengthAlong q hτ
  rw [hpath]
  exact h

/-- **Reduced length data for the Gaussian shrinking soliton model.** -/
def gaussianReducedLengthData (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    ReducedLengthData (gaussianFlow n) 0 q τ where
  path := gaussianLPath (n := n) q hτ
  isMinimizer := gaussian_isLMinimizer q hτ

/-- **Explicit reduced length of the Gaussian model**, through the packaged minimiser:
`l(q, τ) = |q|² / (4 τ)`. -/
theorem gaussianReducedLengthData_reducedLength (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hτ : 0 < τ) :
    (gaussianReducedLengthData (n := n) q hτ).reducedLength = ‖q‖ ^ 2 / (4 * τ) := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  simp only [ReducedLengthData.reducedLength, LPath.reducedLength, LPath.length,
    gaussianReducedLengthData, gaussianLPath]
  rw [gaussian_LlengthAlong q hτ]
  field_simp [hτne]
  rw [Real.sq_sqrt hτ.le]
  ring

/-- **Non-vacuity of the minimiser existence `Prop`.**  For the Gaussian shrinking soliton model,
`LMinimizerExistence` holds: the explicit `L`-geodesic is a minimiser. -/
theorem gaussianLMinimizerExistence (n : ℕ) :
    LMinimizerExistence (gaussianFlow n) 0 := by
  intro q τ hτ
  exact ⟨gaussianLPath (n := n) q hτ, gaussian_isLMinimizer q hτ⟩

end

end Reduced
end D7
end Poincare
