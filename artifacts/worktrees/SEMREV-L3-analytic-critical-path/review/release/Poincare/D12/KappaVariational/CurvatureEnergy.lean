/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-kappa-variational builder
-/
import Poincare.D7.Reduced.Gaussian

/-!
# Poincare.D12.KappaVariational.CurvatureEnergy

**A quantitative curve-energy bound and minimizer for the `L`-length with constant scalar
curvature — a model-space calculation over the D7 `MetricFlowInterface`.**

The D7 layer proved (`Poincare.D7.Reduced.Gaussian.gaussian_length_le`) that for the Gaussian
shrinking soliton (`R ≡ 0`, Euclidean metric) the straight line `γ(σ) = (√σ/√τ) • q` minimises
the `L`-length `L(γ) = ∫₀^τ √σ (R + |γ'|²) dσ` with value `‖q‖² / (2√τ)`.  This file generalises
that quantitative bound to **constant scalar curvature** `R₀ ≥ 0`: the curvature term
`∫₀^τ √σ R₀ dσ = (2/3) R₀ τ^{3/2}` is path-independent, so the same completing-the-square
argument gives, for *every* admissible path `P` from `0` to `q` over `[0, τ]`,

```
‖q‖² / (2√τ) + (2/3) R₀ τ^{3/2} ≤ L(P),
```

with **equality for the straight line**.  The corresponding reduced-length statements are

```
l(q, τ) ≥ ‖q‖² / (4τ) + (R₀/3) τ,   and   l(q, τ) = ‖q‖² / (4τ) + (R₀/3) τ for the minimiser.
```

This is the exact quantitative input used to bound the reduced length from below in constant
curvature (the model case of Perelman's lower estimates for `l`); it is proved on the *real*
admissible-path space `LPath (constantCurvatureFlow n R₀) 0 q τ` of the D7 interface — curves
with explicit endpoints, continuity, differentiability and integrability fields — not on an
arbitrary certificate.  For `R₀ = 0` it reproduces the D7 Gaussian bound, and the constant `R₀`
family proves the D7 state-only `Prop` `LMinimizerExistence` (which was previously known only for
`R ≡ 0`).

**Geometric assumptions (all explicit):** the space is `EuclideanSpace ℝ (Fin n)`, the metric is
the Euclidean inner product (flat), the scalar curvature is the *constant* `R₀ ≥ 0`, the base
point is `0`, and the backward time is `τ > 0`.  No manifold, Ricci-flow equation or general
curvature bound is involved; the general reduced-length differential inequality (RLV-7) remains
a listed missing input.

Everything is proved from the D7 Gaussian argument plus the elementary integral
`∫₀^τ √σ dσ = (2/3) τ^{3/2}` (`integral_rpow`); there is no `sorry`, `axiom`, `unsafe`,
`native_decide` or `proof_wanted` in this file.
-/

open MeasureTheory intervalIntegral Set
open scoped RealInnerProductSpace

namespace Poincare
namespace D12
namespace KappaVariational

open D7.Reduced

noncomputable section

/-! ## 1. The constant-curvature metric-flow interface -/

/-- **Constant scalar curvature model**: the Euclidean metric with scalar curvature `R₀`
(constant in time and space), as a D7 `MetricFlowInterface`. -/
def constantCurvatureFlow (n : ℕ) (R0 : ℝ) : MetricFlowInterface (EuclideanSpace ℝ (Fin n)) where
  scalarCurvature := fun _ _ => R0
  metric := fun _ x y => ⟪x, y⟫
  metric_symm := fun _ x y => (real_inner_comm x y).symm
  metric_self_nonneg := fun _ x => real_inner_self_nonneg (x := x)
  metric_add_left := fun _ x y z => inner_add_left x y z
  metric_smul_left := fun _ c x y => real_inner_smul_left x y c

@[simp] theorem constantCurvatureFlow_scalarCurvature (n : ℕ) (R0 : ℝ) (τ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (constantCurvatureFlow n R0).scalarCurvature τ x = R0 := rfl

@[simp] theorem constantCurvatureFlow_metric (n : ℕ) (R0 : ℝ) (τ : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    (constantCurvatureFlow n R0).metric τ x y = ⟪x, y⟫ := rfl

/-! ## 2. The elementary integral `∫₀^τ √σ dσ = (2/3) τ^{3/2}` -/

/-- `√σ` is interval-integrable on `[0, τ]`. -/
theorem intervalIntegrable_sqrt (τ : ℝ) :
    IntervalIntegrable (fun σ : ℝ => Real.sqrt σ) volume 0 τ :=
  (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := τ) (r := (1 / 2 : ℝ))
      (by norm_num)).congr fun σ _ => by rw [Real.sqrt_eq_rpow]

/-- **`∫₀^τ √σ dσ = (2/3) τ^{3/2}`** (from `integral_rpow` with exponent `1/2`). -/
theorem integral_sqrt (τ : ℝ) :
    ∫ σ in (0 : ℝ)..τ, Real.sqrt σ = (2 / 3) * τ ^ ((3 : ℝ) / 2) := by
  have hrpow : ∫ σ in (0 : ℝ)..τ, σ ^ ((1 : ℝ) / 2) =
      (τ ^ ((1 : ℝ) / 2 + 1) - (0 : ℝ) ^ ((1 : ℝ) / 2 + 1)) / ((1 : ℝ) / 2 + 1) :=
    integral_rpow (a := 0) (b := τ) (r := (1 : ℝ) / 2) (Or.inl (by norm_num))
  have hcongr : ∫ σ in (0 : ℝ)..τ, σ ^ ((1 : ℝ) / 2) =
      ∫ σ in (0 : ℝ)..τ, Real.sqrt σ := by
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [Real.sqrt_eq_rpow]
  rw [← hcongr, hrpow]
  have hexp : (1 : ℝ) / 2 + 1 = (3 : ℝ) / 2 := by norm_num
  rw [hexp, Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0), sub_zero]
  ring_nf

/-! ## 3. Admissible-path comparison between the two flows -/

/-- An admissible path for the constant-curvature flow is admissible for the Gaussian flow (the
metric is the same Euclidean inner product; only the scalar curvature of the interface differs,
which does not enter the `LPath` fields). -/
def toGaussianPath {n : ℕ} (R0 : ℝ) (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (P : LPath (constantCurvatureFlow n R0) 0 q τ) : LPath (gaussianFlow n) 0 q τ where
  curve := P.curve
  velocity := P.velocity
  curve_zero := P.curve_zero
  curve_tau := P.curve_tau
  continuous_curve := P.continuous_curve
  hasDerivAt := P.hasDerivAt
  integrable_energy := by
    simpa [constantCurvatureFlow, gaussianFlow] using P.integrable_energy
  integrable_cross := fun c => by
    simpa [constantCurvatureFlow, gaussianFlow] using P.integrable_cross c

/-! ## 4. The constant-curvature `L`-length lower bound -/

/-- **Constant-curvature curve-energy bound.**  For `R₀ ≥ 0`, every admissible path `P` from
`0` to `q` over `[0, τ]` has `L`-length at least `‖q‖² / (2√τ) + (2/3) R₀ τ^{3/2}`. -/
theorem constantCurvature_length_le (n : ℕ) (R0 : ℝ) (hR0 : 0 ≤ R0)
    (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ)
    (P : LPath (constantCurvatureFlow n R0) 0 q τ) :
    ‖q‖ ^ 2 / (2 * Real.sqrt τ) + (2 / 3) * R0 * τ ^ ((3 : ℝ) / 2) ≤ P.length := by
  have hsqrt : IntervalIntegrable (fun σ : ℝ => Real.sqrt σ) volume 0 τ :=
    intervalIntegrable_sqrt τ
  have hEint : IntervalIntegrable
      (fun σ : ℝ => Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫) volume 0 τ := by
    simpa [constantCurvatureFlow] using P.integrable_energy
  -- (1) The L-length splits into the path-independent curvature term and the energy term.
  have hE : P.length = R0 * (∫ σ in (0 : ℝ)..τ, Real.sqrt σ)
      + ∫ σ in (0 : ℝ)..τ, Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ := by
    simp only [LPath.length, MetricFlowInterface.LlengthAlong, MetricFlowInterface.LIntegrandAlong,
      constantCurvatureFlow]
    calc
      (∫ σ in (0 : ℝ)..τ, Real.sqrt σ * (R0 + ⟪P.velocity σ, P.velocity σ⟫))
          = ∫ σ in (0 : ℝ)..τ, R0 * Real.sqrt σ + Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ := by
            refine intervalIntegral.integral_congr fun σ _ => ?_
            ring
      _ = R0 * (∫ σ in (0 : ℝ)..τ, Real.sqrt σ)
          + ∫ σ in (0 : ℝ)..τ, Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ := by
            rw [intervalIntegral.integral_add (hsqrt.const_mul R0) hEint,
              intervalIntegral.integral_const_mul]
  -- (2) The energy part satisfies the D7 Gaussian bound.
  have hEge : ‖q‖ ^ 2 / (2 * Real.sqrt τ) ≤
      ∫ σ in (0 : ℝ)..τ, Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ := by
    have h := gaussian_length_le q hτ (toGaussianPath R0 q P)
    simpa [LPath.length, toGaussianPath, MetricFlowInterface.LlengthAlong,
      MetricFlowInterface.LIntegrandAlong, gaussianFlow] using h
  -- (3) Combine with the nonnegative curvature term.
  rw [hE, integral_sqrt τ]
  have hcurv : 0 ≤ R0 * ((2 / 3) * τ ^ ((3 : ℝ) / 2)) :=
    mul_nonneg hR0 (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ) / 3) (Real.rpow_nonneg hτ.le _))
  rw [show (2 / 3) * R0 * τ ^ ((3 : ℝ) / 2) = R0 * ((2 / 3) * τ ^ ((3 : ℝ) / 2)) by ring]
  linarith

/-! ## 5. The straight line is the minimiser -/

/-- The straight line `γ(σ) = (√σ/√τ) • q` as an admissible path for the constant-curvature
flow. -/
def constantCurvatureLPath (n : ℕ) (R0 : ℝ) (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hτ : 0 < τ) : LPath (constantCurvatureFlow n R0) 0 q τ where
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
    simpa [constantCurvatureFlow, gaussianLPath] using (gaussianLPath q hτ).integrable_energy
  integrable_cross := fun c => by
    simpa [constantCurvatureFlow, gaussianLPath] using (gaussianLPath q hτ).integrable_cross c

/-- **Explicit `L`-length of the straight line** in constant curvature:
`L(γ) = ‖q‖² / (2√τ) + (2/3) R₀ τ^{3/2}`. -/
theorem constantCurvature_LlengthAlong (n : ℕ) (R0 : ℝ) (q : EuclideanSpace ℝ (Fin n))
    {τ : ℝ} (hτ : 0 < τ) :
    (constantCurvatureFlow n R0).LlengthAlong (gaussianPath q τ) (gaussianVelocity q τ) 0 τ =
      ‖q‖ ^ 2 / (2 * Real.sqrt τ) + (2 / 3) * R0 * τ ^ ((3 : ℝ) / 2) := by
  have hsqrt : IntervalIntegrable (fun σ : ℝ => Real.sqrt σ) volume 0 τ :=
    intervalIntegrable_sqrt τ
  have hgint : IntervalIntegrable
      (fun σ : ℝ => Real.sqrt σ * ⟪gaussianVelocity q τ σ, gaussianVelocity q τ σ⟫) volume 0 τ := by
    simpa [gaussianLPath] using (gaussianLPath q hτ).integrable_energy
  calc
    (constantCurvatureFlow n R0).LlengthAlong (gaussianPath q τ) (gaussianVelocity q τ) 0 τ
        = ∫ σ in (0 : ℝ)..τ,
            Real.sqrt σ * (R0 + ⟪gaussianVelocity q τ σ, gaussianVelocity q τ σ⟫) := by
          simp [MetricFlowInterface.LlengthAlong, MetricFlowInterface.LIntegrandAlong,
            constantCurvatureFlow]
    _ = ∫ σ in (0 : ℝ)..τ, R0 * Real.sqrt σ +
            Real.sqrt σ * ⟪gaussianVelocity q τ σ, gaussianVelocity q τ σ⟫ := by
          refine intervalIntegral.integral_congr fun σ _ => ?_
          ring
    _ = R0 * (∫ σ in (0 : ℝ)..τ, Real.sqrt σ)
          + ∫ σ in (0 : ℝ)..τ,
              Real.sqrt σ * ⟪gaussianVelocity q τ σ, gaussianVelocity q τ σ⟫ := by
          rw [intervalIntegral.integral_add (hsqrt.const_mul R0) hgint,
            intervalIntegral.integral_const_mul]
    _ = R0 * ((2 / 3) * τ ^ ((3 : ℝ) / 2)) + ‖q‖ ^ 2 / (2 * Real.sqrt τ) := by
          rw [integral_sqrt τ]
          have hgl : ∫ σ in (0 : ℝ)..τ,
              Real.sqrt σ * ⟪gaussianVelocity q τ σ, gaussianVelocity q τ σ⟫ =
                ‖q‖ ^ 2 / (2 * Real.sqrt τ) := by
            simpa [MetricFlowInterface.LlengthAlong, MetricFlowInterface.LIntegrandAlong,
              gaussianFlow] using gaussian_LlengthAlong q hτ
          rw [hgl]
    _ = ‖q‖ ^ 2 / (2 * Real.sqrt τ) + (2 / 3) * R0 * τ ^ ((3 : ℝ) / 2) := by
          ring

/-- **Minimality of the straight line in constant curvature.**  For `R₀ ≥ 0` the straight line
is an `L`-length minimiser among all admissible paths. -/
theorem constantCurvature_isLMinimizer (n : ℕ) (R0 : ℝ) (hR0 : 0 ≤ R0)
    (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    IsLMinimizer (constantCurvatureLPath (n := n) R0 q hτ) := by
  intro Q
  have hlen : (constantCurvatureLPath (n := n) R0 q hτ).length =
      ‖q‖ ^ 2 / (2 * Real.sqrt τ) + (2 / 3) * R0 * τ ^ ((3 : ℝ) / 2) := by
    simpa [LPath.length, constantCurvatureLPath] using
      constantCurvature_LlengthAlong (n := n) R0 q hτ
  rw [hlen]
  exact constantCurvature_length_le n R0 hR0 q hτ Q

/-! ## 6. Reduced-length consequences -/

/-- The identity `τ^{3/2} = τ √τ` for `τ ≥ 0`, used to pass from `L`-length to reduced length. -/
theorem rpow_three_halves_eq_mul_sqrt {τ : ℝ} (hτ : 0 < τ) :
    τ ^ ((3 : ℝ) / 2) = τ * Real.sqrt τ := by
  calc
    τ ^ ((3 : ℝ) / 2) = τ ^ (1 + (1 : ℝ) / 2) := by congr 1; norm_num
    _ = τ ^ 1 * τ ^ ((1 : ℝ) / 2) := Real.rpow_add hτ 1 (1 / 2)
    _ = τ * τ ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]
    _ = τ * Real.sqrt τ := by rw [Real.sqrt_eq_rpow]

/-- **Explicit reduced length of the constant-curvature minimiser**:
`l(q, τ) = ‖q‖² / (4τ) + (R₀/3) τ`. -/
theorem constantCurvature_reducedLength (n : ℕ) (R0 : ℝ) (q : EuclideanSpace ℝ (Fin n))
    {τ : ℝ} (hτ : 0 < τ) :
    (constantCurvatureLPath (n := n) R0 q hτ).reducedLength = ‖q‖ ^ 2 / (4 * τ) + (R0 / 3) * τ := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  simp only [LPath.reducedLength, LPath.length, constantCurvatureLPath]
  rw [constantCurvature_LlengthAlong (n := n) R0 q hτ]
  rw [rpow_three_halves_eq_mul_sqrt hτ]
  field_simp [hτne]
  rw [Real.sq_sqrt hτ.le]
  ring

/-- **Constant-curvature reduced-length lower bound.**  For `R₀ ≥ 0`, every admissible path
from `0` to `q` over `[0, τ]` has reduced length at least `‖q‖² / (4τ) + (R₀/3) τ`; the straight
line attains it. -/
theorem constantCurvature_reducedLength_le (n : ℕ) (R0 : ℝ) (hR0 : 0 ≤ R0)
    (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ)
    (P : LPath (constantCurvatureFlow n R0) 0 q τ) :
    ‖q‖ ^ 2 / (4 * τ) + (R0 / 3) * τ ≤ P.reducedLength := by
  have hle : (constantCurvatureLPath (n := n) R0 q hτ).length ≤ P.length :=
    constantCurvature_isLMinimizer n R0 hR0 q hτ P
  have hdiv : 0 ≤ (1 : ℝ) / (2 * Real.sqrt τ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hle hdiv
  have hlhs : (1 / (2 * Real.sqrt τ)) * (constantCurvatureLPath (n := n) R0 q hτ).length =
      ‖q‖ ^ 2 / (4 * τ) + (R0 / 3) * τ := by
    have hlen : (constantCurvatureLPath (n := n) R0 q hτ).length =
        ‖q‖ ^ 2 / (2 * Real.sqrt τ) + (2 / 3) * R0 * τ ^ ((3 : ℝ) / 2) := by
      simpa [LPath.length, constantCurvatureLPath] using
        constantCurvature_LlengthAlong (n := n) R0 q hτ
    rw [hlen]
    rw [rpow_three_halves_eq_mul_sqrt hτ]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hτ)]
    rw [Real.sq_sqrt hτ.le]
    ring
  rw [hlhs] at hmul
  simpa only [LPath.reducedLength] using hmul

/-- **Reduced length data for the constant-curvature model.** -/
def constantCurvatureReducedLengthData (n : ℕ) (R0 : ℝ) (hR0 : 0 ≤ R0)
    (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    ReducedLengthData (constantCurvatureFlow n R0) 0 q τ where
  path := constantCurvatureLPath (n := n) R0 q hτ
  isMinimizer := constantCurvature_isLMinimizer n R0 hR0 q hτ

/-- **Explicit reduced length of the constant-curvature model**, through the packaged
minimiser: `l(q, τ) = ‖q‖² / (4τ) + (R₀/3) τ`. -/
theorem constantCurvatureReducedLengthData_reducedLength (n : ℕ) (R0 : ℝ) (hR0 : 0 ≤ R0)
    (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    (constantCurvatureReducedLengthData n R0 hR0 q hτ).reducedLength =
      ‖q‖ ^ 2 / (4 * τ) + (R0 / 3) * τ := by
  simpa [ReducedLengthData.reducedLength, constantCurvatureReducedLengthData] using
    constantCurvature_reducedLength (n := n) R0 q hτ

/-! ## 7. Non-vacuity: the D7 state-only `Prop` for the constant-curvature family -/

/-- **Non-vacuity of `LMinimizerExistence` beyond `R ≡ 0`.**  For every nonnegative constant
scalar curvature `R₀`, the constant-curvature flow admits an `L`-length minimiser from `0` to
every `q` at every positive backward time (the explicit straight line). -/
theorem constantCurvatureLMinimizerExistence (n : ℕ) (R0 : ℝ) (hR0 : 0 ≤ R0) :
    LMinimizerExistence (constantCurvatureFlow n R0) 0 := by
  intro q τ hτ
  exact ⟨constantCurvatureLPath (n := n) R0 q hτ, constantCurvature_isLMinimizer n R0 hR0 q hτ⟩

/-- **Monotonicity of the model reduced length in the curvature constant.**  For fixed `q, τ`,
`l(q, τ) = ‖q‖²/(4τ) + R₀τ/3` is nondecreasing in `R₀`. -/
theorem constantCurvature_reducedLength_mono_in_R0 (n : ℕ) {R0 R0' : ℝ} (h : R0 ≤ R0')
    (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    ‖q‖ ^ 2 / (4 * τ) + (R0 / 3) * τ ≤ ‖q‖ ^ 2 / (4 * τ) + (R0' / 3) * τ := by
  have hmul : (R0 / 3) * τ ≤ (R0' / 3) * τ :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h (by norm_num)) hτ.le
  linarith

end

end KappaVariational
end D12
end Poincare
