import Poincare.D11.ReducedVolume.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Poincare.D11.ReducedVolume.StraightRays

**D11 reduced volume, Euclidean case, part 2: the `L`-geodesics from the origin are straight
rays.**

On flat `ℝⁿ` (the interface `euclideanFlow`, with `R = 0`) the `L`-length of a curve over
`[0, τ]` is `∫₀^τ √σ |γ'(σ)|² dσ`.  Its Euler-Lagrange structure degenerates to the
completing-the-square identity: for the constant `c = (1/(2√τ)) • x` and every velocity field
`v`,

```
√σ |v(σ)|² - 2 ⟪c, v(σ)⟫ + |c|²/√σ = √σ |v(σ) - (1/√σ) c|² ≥ 0,
```

whose integral over `[0, τ]` is exactly `L(P) - |x|²/(2√τ)` (`flatDeficit_integral`).  This is
the Euclidean case of Perelman's `L`-geodesic minimality computation, and it is **unconditional**:
no curvature bound, no comparison geometry.

## What this file proves

* `straightRay`, `straightRayVelocity` — the straight ray `γ(σ) = (√σ/√τ) • x` from the origin
  to `x` (a straight line through the origin, parametrised by `√σ`) and its velocity.
* `straightRay_length`, `straightRay_reducedLength` — the explicit `L`-length
  `|x|²/(2√τ)` and reduced length `|x|²/(4τ)` of the ray.
* `straightRay_isLMinimizer` — the ray **is** an `L`-length minimiser (via the D7 Gaussian
  model computation of `Poincare.D7.Reduced.Gaussian`).
* `flatDeficit_integral` — the completing-the-square integral identity above.
* `ae_velocity_eq_of_deficit_integral_zero` — if the deficit integrates to zero, the velocity
  is the radial field `(1/√σ) • c` almost everywhere.
* `LMinimizer_eq_straightRay` — **every `L`-minimiser from the origin coincides with the
  straight ray on `[0, τ]`** (uniqueness, unconditional).
* `IsLMinimizer_of_eq_straightRay`, `minimizer_iff_eq_straightRay` — the exact
  characterisation: **the `L`-geodesics from the origin are exactly the straight rays**.
* `euclidean_LMinimizerExistence` — the D7 state-only `Prop` `LMinimizerExistence` is **proved**
  for the flat interface.

Every proof is complete; there is no `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` in this file.
-/

open MeasureTheory intervalIntegral Filter
open Poincare.D7.Reduced
open scoped RealInnerProductSpace Topology

namespace Poincare
namespace D11
namespace ReducedVolume

noncomputable section

variable {n : ℕ}

/-! ## 1. The straight ray from the origin -/

/-- **The straight ray** from the origin to `x` at backward time `τ`:
`γ(σ) = (√σ/√τ) • x`.  The image is the straight line through `0` and `x`; the parameter is
`√σ`, so in the affine parameter `s = √σ` this is the uniform ray `s ↦ (s/√τ) • x`. -/
def straightRay (x : EuclideanSpace ℝ (Fin n)) (τ : ℝ) : ℝ → EuclideanSpace ℝ (Fin n) :=
  fun σ => (Real.sqrt σ / Real.sqrt τ) • x

/-- The velocity of the straight ray: `γ'(σ) = (1/(2√τ√σ)) • x`. -/
def straightRayVelocity (x : EuclideanSpace ℝ (Fin n)) (τ : ℝ) : ℝ → EuclideanSpace ℝ (Fin n) :=
  fun σ => (1 / (2 * Real.sqrt τ * Real.sqrt σ)) • x

/-- The straight ray is (definitionally) the `L`-geodesic `gaussianPath` of the D7 Gaussian
model. -/
@[simp] theorem straightRay_eq_gaussianPath (x : EuclideanSpace ℝ (Fin n)) (τ : ℝ) :
    straightRay x τ = gaussianPath x τ := rfl

/-- The straight-ray velocity is (definitionally) the velocity `gaussianVelocity` of the D7
Gaussian model. -/
@[simp] theorem straightRayVelocity_eq_gaussianVelocity (x : EuclideanSpace ℝ (Fin n)) (τ : ℝ) :
    straightRayVelocity x τ = gaussianVelocity x τ := rfl

/-- The straight ray starts at the origin. -/
@[simp] theorem straightRay_zero (x : EuclideanSpace ℝ (Fin n)) (τ : ℝ) :
    straightRay x τ 0 = 0 := by
  simp [straightRay]

/-- The straight ray reaches `x` at backward time `τ`. -/
theorem straightRay_tau (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    straightRay x τ τ = x := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  simp [straightRay, div_self hτne]

/-- The straight ray has the stated velocity at every positive time. -/
theorem straightRay_hasDerivAt (x : EuclideanSpace ℝ (Fin n)) {τ σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (straightRay x τ) (straightRayVelocity x τ σ) σ := by
  simpa [straightRay_eq_gaussianPath, straightRayVelocity_eq_gaussianVelocity] using
    gaussianPath_hasDerivAt x hσ

/-- The straight ray as an admissible path for the `L`-length minimisation problem. -/
def straightRayLPath (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    LPath (euclideanFlow n) 0 x τ :=
  gaussianLPath (n := n) x hτ

/-- **Explicit `L`-length of the straight ray**: `L(γ) = |x|²/(2√τ)`. -/
theorem straightRay_length (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    (euclideanFlow n).LlengthAlong (straightRay x τ) (straightRayVelocity x τ) 0 τ =
      ‖x‖ ^ 2 / (2 * Real.sqrt τ) := by
  simpa [straightRay_eq_gaussianPath, straightRayVelocity_eq_gaussianVelocity, euclideanFlow]
    using gaussian_LlengthAlong (n := n) x hτ

/-- **Explicit reduced length of the straight ray**: `ℓ = |x|²/(4τ)`. -/
theorem straightRay_reducedLength (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    (euclideanFlow n).reducedLengthAlong (straightRay x τ) (straightRayVelocity x τ) τ =
      ‖x‖ ^ 2 / (4 * τ) := by
  simpa [straightRay_eq_gaussianPath, straightRayVelocity_eq_gaussianVelocity, euclideanFlow]
    using gaussian_reducedLengthAlong (n := n) x hτ

/-- The heat-kernel-asymptotics reduced distance equals the reduced length of the straight
ray: both are `|x|²/(4τ)`. -/
theorem heatKernelReducedDistance_eq_straightRayReducedLength (x : EuclideanSpace ℝ (Fin n))
    {τ : ℝ} (hτ : 0 < τ) :
    heatKernelReducedDistance n τ x =
      (euclideanFlow n).reducedLengthAlong (straightRay x τ) (straightRayVelocity x τ) τ := by
  rw [heatKernelReducedDistance_eq hτ, straightRay_reducedLength x hτ]

/-- **The straight ray is an `L`-length minimiser** among admissible paths from the origin to
`x`. -/
theorem straightRay_isLMinimizer (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    IsLMinimizer (straightRayLPath (n := n) x hτ) := by
  exact gaussian_isLMinimizer (n := n) x hτ

/-- **Non-vacuity of minimiser existence for the flat interface.**  The D7 state-only `Prop`
`LMinimizerExistence` holds for `euclideanFlow`: the explicit straight ray is a minimiser. -/
theorem euclidean_LMinimizerExistence (n : ℕ) :
    LMinimizerExistence (euclideanFlow n) 0 := by
  intro q τ hτ
  exact ⟨straightRayLPath (n := n) q hτ, straightRay_isLMinimizer q hτ⟩

/-! ## 2. The completing-the-square deficit -/

/-- **The completing-the-square deficit** of a velocity `v` against the constant `c`:
`√σ |v|² - 2 ⟪c, v⟫ + |c|²/√σ`.  Its integral over `[0, τ]` is the excess of the `L`-length of
the path with velocity `v` over the minimal length (see `flatDeficit_integral`). -/
def flatDeficit (c v : EuclideanSpace ℝ (Fin n)) (σ : ℝ) : ℝ :=
  Real.sqrt σ * ⟪v, v⟫ - 2 * ⟪c, v⟫ + ⟪c, c⟫ / Real.sqrt σ

/-- The completing-the-square identity: for `σ > 0`,
`√σ |v|² - 2 ⟪c, v⟫ + |c|²/√σ = √σ |v - (1/√σ) c|²`. -/
theorem flatDeficit_eq_normSq (c v : EuclideanSpace ℝ (Fin n)) {σ : ℝ} (hσ : 0 < σ) :
    flatDeficit c v σ = Real.sqrt σ * ‖v - (1 / Real.sqrt σ) • c‖ ^ 2 := by
  unfold flatDeficit
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_right, real_inner_smul_left,
    real_inner_comm v c]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hσ)]
  ring

/-- The deficit is nonnegative for positive times. -/
theorem flatDeficit_nonneg (c v : EuclideanSpace ℝ (Fin n)) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ flatDeficit c v σ := by
  rw [flatDeficit_eq_normSq c v hσ]
  exact mul_nonneg (Real.sqrt_nonneg σ) (sq_nonneg ‖v - (1 / Real.sqrt σ) • c‖)

/-- **The integral identity behind the straight-ray minimality.**  For an admissible path `P`
from the origin to `x` and `c = (1/(2√τ)) • x`,

```
∫₀^τ (√σ |P'(σ)|² - 2 ⟪c, P'(σ)⟫ + |c|²/√σ) dσ = L(P) - |x|²/(2√τ).
```

The proof is the fundamental theorem of calculus for the cross term
(`∫₀^τ ⟪c, P'(σ)⟫ dσ = ⟪c, x⟫`) plus `∫₀^τ σ^{-1/2} dσ = 2√τ` (`integral_one_div_sqrt` of
the D7 Gaussian model). -/
theorem flatDeficit_integral (c x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ)
    (hc : c = (1 / (2 * Real.sqrt τ)) • x) (P : LPath (euclideanFlow n) 0 x τ) :
    ∫ σ in (0 : ℝ)..τ, flatDeficit c (P.velocity σ) σ = P.length - ‖x‖ ^ 2 / (2 * Real.sqrt τ) := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  -- (1) The cross term integrates to `⟪c, x⟫` by the fundamental theorem of calculus.
  have hcross : ∫ σ in (0 : ℝ)..τ, ⟪c, P.velocity σ⟫ = ⟪c, x⟫ := by
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
  -- (2) Integrability of the three pieces of the deficit.
  have hIntEnergy : IntervalIntegrable
      (fun σ : ℝ => Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫) volume 0 τ := by
    simpa [euclideanFlow] using P.integrable_energy
  have hIntCross : IntervalIntegrable (fun σ : ℝ => ⟪c, P.velocity σ⟫) volume 0 τ := by
    simpa [euclideanFlow] using P.integrable_cross c
  have hIntInv : IntervalIntegrable (fun σ : ℝ => ⟪c, c⟫ / Real.sqrt σ) volume 0 τ := by
    refine ((intervalIntegrable_one_div_sqrt hτ).const_mul ⟪c, c⟫).congr fun σ _ => ?_
    rw [div_eq_mul_inv]
    ring
  have hInvMul : ∫ σ in (0 : ℝ)..τ, ⟪c, c⟫ / Real.sqrt σ = ⟪c, c⟫ * (2 * Real.sqrt τ) := by
    rw [← integral_one_div_sqrt hτ.le, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [div_eq_mul_inv]
    ring
  -- (3) The integral of the deficit.
  have hfint : ∫ σ in (0 : ℝ)..τ,
      (Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ - 2 * ⟪c, P.velocity σ⟫
        + ⟪c, c⟫ / Real.sqrt σ) =
      (∫ σ in (0 : ℝ)..τ, Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫)
        - 2 * (∫ σ in (0 : ℝ)..τ, ⟪c, P.velocity σ⟫)
        + ⟪c, c⟫ * (2 * Real.sqrt τ) := by
    rw [intervalIntegral.integral_add (hIntEnergy.sub (hIntCross.const_mul 2)) hIntInv,
      intervalIntegral.integral_sub hIntEnergy (hIntCross.const_mul 2),
      intervalIntegral.integral_const_mul, hInvMul]
  -- (4) The `L`-length of `P` is the energy integral.
  have hlength : P.length = ∫ σ in (0 : ℝ)..τ,
      Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ := by
    simp [LPath.length, MetricFlowInterface.LlengthAlong, MetricFlowInterface.LIntegrandAlong,
      euclideanFlow, gaussianFlow]
  -- (5) The constants `⟪c, x⟫` and `⟪c, c⟫`.
  have hcq : ⟪c, x⟫ = (1 / (2 * Real.sqrt τ)) * ‖x‖ ^ 2 := by
    rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hcc : ⟪c, c⟫ = (1 / (2 * Real.sqrt τ)) ^ 2 * ‖x‖ ^ 2 := by
    rw [hc, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  -- (6) Combine.
  unfold flatDeficit
  rw [hfint, hcross, ← hlength, hcq, hcc]
  have hgoal : P.length - 2 * ((1 / (2 * Real.sqrt τ)) * ‖x‖ ^ 2)
      + (1 / (2 * Real.sqrt τ)) ^ 2 * ‖x‖ ^ 2 * (2 * Real.sqrt τ)
      = P.length - ‖x‖ ^ 2 / (2 * Real.sqrt τ) := by
    field_simp [hτne]
    ring
  rw [hgoal]

/-- **Vanishing deficit forces the radial velocity field.**  If the deficit of an admissible
path integrates to zero, then `P'(σ) = (1/√σ) • c` almost everywhere on `(0, τ]`: the
completing-the-square identity writes the deficit as `√σ |P'(σ) - (1/√σ) c|² ≥ 0`, and a
nonnegative integrable function with zero integral vanishes almost everywhere
(`MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`).  The intended instantiation is
`c = (1/(2√τ)) • x`, the constant of `flatDeficit_integral`. -/
theorem ae_velocity_eq_of_deficit_integral_zero (c : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} {τ : ℝ} (hτ : 0 < τ) (P : LPath (euclideanFlow n) 0 x τ)
    (hz : ∫ σ in (0 : ℝ)..τ, flatDeficit c (P.velocity σ) σ = 0) :
    ∀ᵐ σ ∂volume.restrict (Set.Ioc (0 : ℝ) τ), P.velocity σ = (1 / Real.sqrt σ) • c := by
  -- (1) The deficit is nonnegative on `(0, τ]`.
  have hnonneg_ae : ∀ᵐ σ ∂volume.restrict (Set.Ioc (0 : ℝ) τ),
      0 ≤ flatDeficit c (P.velocity σ) σ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with σ
    intro hσ
    exact flatDeficit_nonneg c (P.velocity σ) hσ.1
  -- (2) The deficit is integrable on the restricted measure.
  have hIntegrable : Integrable (fun σ => flatDeficit c (P.velocity σ) σ)
      (volume.restrict (Set.Ioc (0 : ℝ) τ)) := by
    have hE : Integrable (fun σ => Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫)
        (volume.restrict (Set.Ioc (0 : ℝ) τ)) := by
      exact P.integrable_energy.1
    have hC : Integrable (fun σ => ⟪c, P.velocity σ⟫) (volume.restrict (Set.Ioc (0 : ℝ) τ)) := by
      exact (P.integrable_cross c).1
    have hI : Integrable (fun σ => ⟪c, c⟫ / Real.sqrt σ)
        (volume.restrict (Set.Ioc (0 : ℝ) τ)) := by
      have hII : IntervalIntegrable (fun σ : ℝ => ⟪c, c⟫ / Real.sqrt σ) volume 0 τ := by
        refine ((intervalIntegrable_one_div_sqrt hτ).const_mul ⟪c, c⟫).congr fun σ _ => ?_
        rw [div_eq_mul_inv]
        ring
      exact hII.1
    unfold flatDeficit
    exact (hE.sub (hC.const_mul 2)).add hI
  -- (3) Zero integral ⇒ zero almost everywhere.
  have hzero : (∫ σ, flatDeficit c (P.velocity σ) σ ∂volume.restrict (Set.Ioc (0 : ℝ) τ)) = 0 := by
    rw [← intervalIntegral.integral_of_le hτ.le]
    exact hz
  have hfae : (fun σ => flatDeficit c (P.velocity σ) σ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) τ)] 0 := by
    have hiff := MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (μ := volume.restrict (Set.Ioc (0 : ℝ) τ)) (f := fun σ => flatDeficit c (P.velocity σ) σ)
      hnonneg_ae hIntegrable
    exact hiff.mp hzero
  -- (4) On the residual set the velocity is the radial field.
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Ioc).1 hfae] with σ hf0
  intro hσ
  have hσpos : 0 < σ := hσ.1
  have hσne : Real.sqrt σ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hσpos)
  have hid : flatDeficit c (P.velocity σ) σ =
      Real.sqrt σ * ‖P.velocity σ - (1 / Real.sqrt σ) • c‖ ^ 2 :=
    flatDeficit_eq_normSq c (P.velocity σ) hσpos
  have hzero' : Real.sqrt σ * ‖P.velocity σ - (1 / Real.sqrt σ) • c‖ ^ 2 = 0 := by
    rw [← hid]
    simpa using hf0 hσ
  have hnorm_sq : ‖P.velocity σ - (1 / Real.sqrt σ) • c‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hzero').resolve_left (ne_of_gt (Real.sqrt_pos.2 hσpos))
  have hnorm : ‖P.velocity σ - (1 / Real.sqrt σ) • c‖ = 0 := sq_eq_zero_iff.mp hnorm_sq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-! ## 3. Every `L`-minimiser from the origin is the straight ray -/

/-- **Uniqueness: every `L`-minimiser from the origin in flat `ℝⁿ` is the straight ray.**

An admissible path `P` from `0` to `x` minimising the `L`-length must have
`L(P) = |x|²/(2√τ)` (minimality of the ray, `straightRay_isLMinimizer`), so the deficit
integrates to zero (`flatDeficit_integral`), the velocity is the radial field
`(1/√σ) • c` with `c = (1/(2√τ)) • x` almost everywhere
(`ae_velocity_eq_of_deficit_integral_zero`), and the fundamental theorem of calculus on
`[0, σ₀]` gives `P(σ₀) = 2√σ₀ • c = (√σ₀/√τ) • x`. -/
theorem LMinimizer_eq_straightRay (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ)
    (P : LPath (euclideanFlow n) 0 x τ) (hmin : IsLMinimizer P) :
    ∀ σ ∈ Set.Icc (0 : ℝ) τ, P.curve σ = straightRay x τ σ := by
  have hτne : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hτ)
  set c : EuclideanSpace ℝ (Fin n) := (1 / (2 * Real.sqrt τ)) • x with hc
  -- (0) The `L`-length of `P` attains the minimal value `|x|²/(2√τ)`.
  have hraylen : (straightRayLPath (n := n) x hτ).length = ‖x‖ ^ 2 / (2 * Real.sqrt τ) := by
    change (euclideanFlow n).LlengthAlong (gaussianPath x τ) (gaussianVelocity x τ) 0 τ =
      ‖x‖ ^ 2 / (2 * Real.sqrt τ)
    exact gaussian_LlengthAlong (n := n) x hτ
  have hlen : P.length = ‖x‖ ^ 2 / (2 * Real.sqrt τ) := by
    have hle : P.length ≤ (straightRayLPath (n := n) x hτ).length :=
      hmin (straightRayLPath (n := n) x hτ)
    have hge : ‖x‖ ^ 2 / (2 * Real.sqrt τ) ≤ P.length := gaussian_length_le (n := n) x hτ P
    rw [hraylen] at hle
    linarith
  -- (1) Hence the deficit integrates to zero.
  have hz : ∫ σ in (0 : ℝ)..τ, flatDeficit c (P.velocity σ) σ = 0 := by
    rw [flatDeficit_integral c x hτ hc P, hlen]
    ring
  -- (2) Hence the velocity is the radial field almost everywhere.
  have hae : ∀ᵐ σ ∂volume.restrict (Set.Ioc (0 : ℝ) τ), P.velocity σ = (1 / Real.sqrt σ) • c :=
    ae_velocity_eq_of_deficit_integral_zero c hτ P hz
  -- (3) Integrate on `[0, σ₀]` to recover the curve.
  intro σ₀ hσ₀
  by_cases hσ₀eq0 : σ₀ = 0
  · subst hσ₀eq0
    simpa [straightRay] using P.curve_zero
  · have hσ₀pos : 0 < σ₀ := lt_of_le_of_ne hσ₀.1 (Ne.symm hσ₀eq0)
    have hσ₀le : σ₀ ≤ τ := hσ₀.2
    have hIconst : IntervalIntegrable (fun σ : ℝ => (1 / Real.sqrt σ) • c) volume 0 σ₀ :=
      (intervalIntegrable_one_div_sqrt (τ := σ₀) hσ₀pos).smul_continuousOn continuousOn_const
    have hae₀ : ∀ᵐ σ ∂volume.restrict (Set.Ioc (0 : ℝ) σ₀),
        P.velocity σ = (1 / Real.sqrt σ) • c := by
      exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (by intro σ hσ; exact ⟨hσ.1, le_trans hσ.2 hσ₀le⟩) hae
    have hIvel : IntervalIntegrable P.velocity volume 0 σ₀ := by
      refine hIconst.congr_ae ?_
      rw [Set.uIoc_of_le hσ₀pos.le]
      filter_upwards [hae₀] with σ h
      exact h.symm
    have hcont : ContinuousOn P.curve (Set.Icc (0 : ℝ) σ₀) :=
      P.continuous_curve.mono (by intro σ hσ; exact ⟨hσ.1, le_trans hσ.2 hσ₀le⟩)
    have hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) σ₀, HasDerivAt P.curve (P.velocity σ) σ := by
      intro σ hσ
      exact P.hasDerivAt σ ⟨hσ.1, lt_of_lt_of_le hσ.2 hσ₀le⟩
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hσ₀pos.le hcont hderiv hIvel
    have hcongr : ∫ σ in (0 : ℝ)..σ₀, P.velocity σ =
        ∫ σ in (0 : ℝ)..σ₀, (1 / Real.sqrt σ) • c := by
      rw [intervalIntegral.integral_of_le hσ₀pos.le, intervalIntegral.integral_of_le hσ₀pos.le]
      exact MeasureTheory.integral_congr_ae hae₀
    have hIconstInt : ∫ σ in (0 : ℝ)..σ₀, (1 / Real.sqrt σ) • c = (2 * Real.sqrt σ₀) • c := by
      rw [intervalIntegral.integral_smul_const, integral_one_div_sqrt hσ₀pos.le]
    have hcurve : P.curve σ₀ - P.curve 0 = (2 * Real.sqrt σ₀) • c := by
      rw [← hFTC, hcongr, hIconstInt]
    have hcurve' : P.curve σ₀ = (2 * Real.sqrt σ₀) • c := by
      rw [P.curve_zero] at hcurve
      simpa using hcurve
    rw [hcurve', hc, straightRay]
    rw [smul_smul]
    congr 1
    field_simp [hτne]

/-- **Converse: a path that stays on the straight ray is an `L`-minimiser.**  Its velocity is
the radial velocity field of the ray wherever both are differentiable, so its `L`-length is the
minimal `|x|²/(2√τ)`. -/
theorem IsLMinimizer_of_eq_straightRay (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ)
    (P : LPath (euclideanFlow n) 0 x τ)
    (hEq : ∀ σ ∈ Set.Icc (0 : ℝ) τ, P.curve σ = straightRay x τ σ) : IsLMinimizer P := by
  have hvel : ∀ σ ∈ Set.Ioo (0 : ℝ) τ, P.velocity σ = straightRayVelocity x τ σ := by
    intro σ hσ
    have hnear : P.curve =ᶠ[𝓝 σ] straightRay x τ := by
      filter_upwards [Ioo_mem_nhds hσ.1 hσ.2] with s hs
      exact hEq s ⟨hs.1.le, hs.2.le⟩
    have hd : HasDerivAt P.curve (straightRayVelocity x τ σ) σ :=
      (straightRay_hasDerivAt x hσ.1).congr_of_eventuallyEq hnear
    exact (P.hasDerivAt σ hσ).unique hd
  have hcongr_ae : ∀ᵐ σ ∂volume, σ ∈ Set.uIoc (0 : ℝ) τ →
      Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ =
        Real.sqrt σ * ⟪straightRayVelocity x τ σ, straightRayVelocity x τ σ⟫ := by
    rw [Set.uIoc_of_le hτ.le]
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (by simp : volume ({τ} : Set ℝ) = 0)
    intro σ hσ
    rw [Set.mem_ofPred_eq] at hσ
    simp only [not_imp, Set.mem_Ioc] at hσ
    by_contra hne
    have hσioo : σ ∈ Set.Ioo (0 : ℝ) τ := ⟨hσ.1.1, lt_of_le_of_ne hσ.1.2 hne⟩
    exact hσ.2 (by rw [hvel σ hσioo])
  have hlen : P.length = ‖x‖ ^ 2 / (2 * Real.sqrt τ) := by
    unfold LPath.length MetricFlowInterface.LlengthAlong MetricFlowInterface.LIntegrandAlong
    simp only [euclideanFlow_scalarCurvature, euclideanFlow_metric, zero_add]
    have hcongr2 : ∫ σ in (0 : ℝ)..τ, Real.sqrt σ * ⟪P.velocity σ, P.velocity σ⟫ =
        ∫ σ in (0 : ℝ)..τ,
          Real.sqrt σ * ⟪straightRayVelocity x τ σ, straightRayVelocity x τ σ⟫ :=
      intervalIntegral.integral_congr_ae hcongr_ae
    rw [hcongr2]
    have hray : ∫ σ in (0 : ℝ)..τ,
        Real.sqrt σ * ⟪straightRayVelocity x τ σ, straightRayVelocity x τ σ⟫ =
        ‖x‖ ^ 2 / (2 * Real.sqrt τ) := by
      have h := straightRay_length x hτ
      unfold MetricFlowInterface.LlengthAlong MetricFlowInterface.LIntegrandAlong at h
      simp only [euclideanFlow_scalarCurvature, euclideanFlow_metric, zero_add] at h
      exact h
    exact hray
  intro Q
  have hle : ‖x‖ ^ 2 / (2 * Real.sqrt τ) ≤ Q.length := gaussian_length_le (n := n) x hτ Q
  rwa [hlen]

/-- **Characterisation: the `L`-geodesics from the origin in flat `ℝⁿ` are exactly the
straight rays.**  An admissible path from `0` to `x` over `[0, τ]` minimises the `L`-length if
and only if it coincides with `γ(σ) = (√σ/√τ) • x` on `[0, τ]`. -/
theorem minimizer_iff_eq_straightRay (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ)
    (P : LPath (euclideanFlow n) 0 x τ) :
    IsLMinimizer P ↔ ∀ σ ∈ Set.Icc (0 : ℝ) τ, P.curve σ = straightRay x τ σ :=
  ⟨LMinimizer_eq_straightRay x hτ P, IsLMinimizer_of_eq_straightRay x hτ P⟩

end

end ReducedVolume
end D11
end Poincare
