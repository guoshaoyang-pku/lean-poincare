/-
Copyright (c) 2026 Poincare Longrun D12 semantic-ledger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-semantic-ledger)
-/

import Mathlib

set_option linter.unusedVariables false

/-!
# Poincare.D12.SemanticLedger.Defect

**Adversarial-audit validation of the D7 heat-kernel initial-condition field.**

## What is audited

The D7-heat-kernel-existence task released
`release/Poincare/D7/HeatKernel/Basic.lean` (sha256 recorded in the ledger)
containing the structure `Poincare.D7.HeatKernel.HeatKernelData` whose field
`initialCondition` (source lines 100-103) reads, verbatim:

```
initialCondition : ∀ (x : X) (f : X → ℝ), Continuous f →
  Tendsto (fun t : ℝ => ∫ y, kernel x y t * f y ∂volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))
```

The hypothesis on the test function is **only** `Continuous f`, with no
integrability, boundedness, compact-support or growth condition.  On a
noncompact state space `X` with a finite-mass kernel this requirement is
overstrong: a continuous test function growing faster than the Gaussian decay
of the kernel makes the integrand non-integrable for every `t > 0`, so the
(undefined, hence `0` by the mathlib Bochner convention) integral cannot
converge to `f x ≠ 0`.  This file proves that failure **for the standard
Euclidean heat kernel on `ℝ`**:

* `gaussianKernelXY x y t = (4πt) ^ (-1/2) * exp (-(x-y)² / (4t))` is the
  explicit 1-dimensional Gaussian heat kernel (the same mathematical object as
  `Poincare.D10.HeatKernelEuclidean.gaussianKernel 1` after the canonical
  identification of `ℝ` with `EuclideanSpace ℝ (Fin 1)`; the D10 development
  itself proves no initial-condition theorem for it),
* `testFunction y = exp (y⁴)` is a continuous, unbounded test function,
* for every `t > 0` the integrand `y ↦ gaussianKernelXY x y t * testFunction y`
  is **not integrable** with respect to Lebesgue measure, because it is bounded
  below by a positive constant on a half-line of infinite measure,
* hence `∫ y, gaussianKernelXY x y t * testFunction y ∂volume = 0` for every
  `t > 0`, while `testFunction 0 = 1`.

Consequently the field, quantified over *all* continuous test functions, is
false for this kernel, i.e. no heat-kernel datum on `ℝ` whose kernel is the
standard Gaussian and whose volume is Lebesgue measure can satisfy the D7
`initialCondition` field.  This is the precise semantic content of the
"all continuous functions on noncompact Euclidean space is overstrong" defect
tracked by `D12-heat-domain-repair`; the repair (an admissible-test-function
interface such as continuous compact support or an explicit integrable class)
is **not** attempted here and remains an open dependency request.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted` occurs in this file.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.D12.SemanticLedger

/-! ## 1. The observed interface (verbatim restatement, `x` specialized to a fixed base point) -/

/-- The standard one-dimensional Euclidean heat kernel, written in the field order
`kernel x y t` used by `HeatKernelData.kernel`. -/
noncomputable def gaussianKernelXY (x y t : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(x - y) ^ 2 / (4 * t))

/-- The D7 `HeatKernelData.initialCondition` statement (verbatim from
`Poincare/D7/HeatKernel/Basic.lean` lines 100-103, source hash in the ledger),
instantiated on `X = ℝ` with `volume` = Lebesgue measure, a kernel `K : ℝ → ℝ → ℝ → ℝ`
and a fixed base point `x`.  The test-function hypothesis is exactly
`Continuous f` — no integrability or growth condition. -/
def D7InitialConditionAt (K : ℝ → ℝ → ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun t : ℝ => ∫ y, K x y t * f y ∂volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x))

/-! ## 2. The unbounded continuous test function -/

/-- The concrete test function `y ↦ exp (y⁴)`: continuous, positive, unbounded, and
`1` at the origin.  It is continuous but has no finite integral against the Gaussian
kernel for any `t > 0`. -/
noncomputable def testFunction (y : ℝ) : ℝ := Real.exp (y ^ 4)

theorem testFunction_continuous : Continuous testFunction := by
  unfold testFunction
  exact Real.continuous_exp.comp (continuous_id.pow 4)

theorem testFunction_pos (y : ℝ) : 0 < testFunction y := by
  unfold testFunction
  exact Real.exp_pos _

theorem testFunction_zero : testFunction 0 = 1 := by
  unfold testFunction
  norm_num

theorem tendsto_testFunction_atTop : Tendsto testFunction atTop atTop := by
  have h4 : Tendsto (fun y : ℝ => y ^ 4) atTop atTop := by
    have h2 : Tendsto (fun y : ℝ => y * y) atTop atTop :=
      tendsto_id.atTop_mul_atTop₀ tendsto_id
    have h3 : Tendsto (fun y : ℝ => y * y * y) atTop atTop :=
      h2.atTop_mul_atTop₀ tendsto_id
    have h4' : Tendsto (fun y : ℝ => y * y * y * y) atTop atTop :=
      h3.atTop_mul_atTop₀ tendsto_id
    simpa [pow_succ, pow_two, mul_assoc] using h4'
  unfold testFunction
  exact Real.tendsto_exp_atTop.comp h4

/-! ## 3. The integrand is bounded below by a positive constant on a half-line -/

/-- The threshold after which the quartic term dominates the Gaussian decay:
for `y ≥ R t` one has `y²/(4t) ≤ y⁴/2`. -/
noncomputable def R (t : ℝ) : ℝ := Real.sqrt (1 / (2 * t))

/-- The positive lower constant on `[R t, ∞)`: the integrand at the threshold is
`(4πt)^(-1/2) * exp ((R t)⁴ / 2)`. -/
noncomputable def lowerConstant (t : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp ((R t) ^ 4 / 2)

theorem R_sq (t : ℝ) (ht : 0 < t) : (R t) ^ 2 = 1 / (2 * t) := by
  unfold R
  rw [Real.sq_sqrt]
  positivity

theorem R_nonneg (t : ℝ) : 0 ≤ R t := by
  unfold R
  exact Real.sqrt_nonneg _

theorem lowerConstant_pos (t : ℝ) (ht : 0 < t) : 0 < lowerConstant t := by
  unfold lowerConstant
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- The integrand of the D7 initial-condition integral for the Gaussian kernel at
base point `0` and test function `testFunction`. -/
noncomputable def integrand (t y : ℝ) : ℝ := gaussianKernelXY 0 y t * testFunction y

theorem integrand_eq (t : ℝ) (ht : 0 < t) (y : ℝ) :
    integrand t y =
      (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (y ^ 4 - y ^ 2 / (4 * t)) := by
  unfold integrand gaussianKernelXY testFunction
  have hne : 4 * t ≠ 0 := by positivity
  calc
    (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(0 - y) ^ 2 / (4 * t)) * Real.exp (y ^ 4)
        = (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) *
            (Real.exp (-(0 - y) ^ 2 / (4 * t)) * Real.exp (y ^ 4)) := by
          rw [mul_assoc]
    _ = (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) *
            Real.exp (-(0 - y) ^ 2 / (4 * t) + y ^ 4) := by
          rw [← Real.exp_add]
    _ = (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (y ^ 4 - y ^ 2 / (4 * t)) := by
          congr 2
          field_simp [hne]
          ring

theorem integrand_nonneg (t : ℝ) (ht : 0 < t) (y : ℝ) : 0 ≤ integrand t y := by
  rw [integrand_eq t ht y]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_of_lt (Real.exp_pos _))

/-- On the half-line `[R t, ∞)` the quartic exponent dominates the Gaussian decay:
`y⁴ - y²/(4t) ≥ y⁴/2`. -/
theorem quartic_dominates (t : ℝ) (ht : 0 < t) {y : ℝ} (hy : y ∈ Set.Ici (R t)) :
    y ^ 4 / 2 ≤ y ^ 4 - y ^ 2 / (4 * t) := by
  have hR0 := R_nonneg t
  have hRy : R t ≤ y := hy
  have hy0 : 0 ≤ y := le_trans hR0 hRy
  have hy2 : 1 / (2 * t) ≤ y ^ 2 := by
    rw [← R_sq t ht]
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hR0, abs_of_nonneg hy0] using hRy)
  have hdom : y ^ 2 / (4 * t) ≤ y ^ 4 / 2 := by
    calc
      y ^ 2 / (4 * t) = (1 / (2 * t)) * (y ^ 2 / 2) := by ring
      _ ≤ y ^ 2 * (y ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hy2 (by positivity)
      _ = y ^ 4 / 2 := by ring
  linarith

/-- The integrand is bounded below by the positive constant `lowerConstant t`
on `[R t, ∞)`. -/
theorem lowerConstant_le_integrand (t : ℝ) (ht : 0 < t) {y : ℝ} (hy : y ∈ Set.Ici (R t)) :
    lowerConstant t ≤ integrand t y := by
  rw [integrand_eq t ht y]
  unfold lowerConstant
  have hR0 := R_nonneg t
  have hRy : R t ≤ y := hy
  have hy0 : 0 ≤ y := le_trans hR0 hRy
  have hR4le : (R t) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hR0 hRy 4
  have hexp1 : Real.exp ((R t) ^ 4 / 2) ≤ Real.exp (y ^ 4 / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hR4le (by norm_num))
  have hexp2 : Real.exp (y ^ 4 / 2) ≤ Real.exp (y ^ 4 - y ^ 2 / (4 * t)) :=
    Real.exp_le_exp.mpr (quartic_dominates t ht hy)
  have hpref : 0 ≤ (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  calc
    (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp ((R t) ^ 4 / 2)
        ≤ (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (y ^ 4 / 2) :=
          mul_le_mul_of_nonneg_left hexp1 hpref
    _ ≤ (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (y ^ 4 - y ^ 2 / (4 * t)) :=
          mul_le_mul_of_nonneg_left hexp2 hpref

/-! ## 4. Non-integrability: the `ℝ≥0∞` integral of the integrand is `∞` for every `t > 0` -/

theorem continuous_gaussianKernelXY_int (t : ℝ) :
    Continuous (fun y : ℝ => gaussianKernelXY 0 y t) := by
  unfold gaussianKernelXY
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  continuity

theorem integrand_continuous (t : ℝ) : Continuous (fun y : ℝ => integrand t y) := by
  unfold integrand
  exact (continuous_gaussianKernelXY_int t).mul testFunction_continuous

theorem integrand_pos (t : ℝ) (ht : 0 < t) (y : ℝ) : 0 < integrand t y := by
  rw [integrand_eq t ht y]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem integrand_lintegral_eq_top (t : ℝ) (ht : 0 < t) :
    ∫⁻ y, ENNReal.ofReal (integrand t y) ∂volume = ∞ := by
  let s : Set ℝ := Set.Ici (R t)
  have hc0 : (0 : ℝ) < lowerConstant t := lowerConstant_pos t ht
  have hset : ∫⁻ _ in s, ENNReal.ofReal (lowerConstant t) ∂volume = ∞ := by
    dsimp [s]
    calc
      ∫⁻ _ in Set.Ici (R t), ENNReal.ofReal (lowerConstant t) ∂volume
          = ENNReal.ofReal (lowerConstant t) * volume (Set.Ici (R t)) := by
            rw [setLIntegral_const]
      _ = ENNReal.ofReal (lowerConstant t) * ∞ := by rw [Real.volume_Ici]
      _ = ∞ := ENNReal.mul_top ((ENNReal.ofReal_pos.mpr hc0).ne')
  have hmono_set : ∫⁻ y in s, ENNReal.ofReal (lowerConstant t) ∂volume ≤
      ∫⁻ y in s, ENNReal.ofReal (integrand t y) ∂volume := by
    apply setLIntegral_mono
    · exact (ENNReal.continuous_ofReal.comp (integrand_continuous t)).measurable
    · intro y hy
      dsimp [s] at hy
      exact ENNReal.ofReal_le_ofReal (lowerConstant_le_integrand t ht hy)
  have hle_univ : ∫⁻ y in s, ENNReal.ofReal (integrand t y) ∂volume ≤
      ∫⁻ y, ENNReal.ofReal (integrand t y) ∂volume :=
    setLIntegral_le_lintegral s (fun y => ENNReal.ofReal (integrand t y))
  exact eq_top_iff.mpr (le_trans (le_of_eq hset.symm) (le_trans hmono_set hle_univ))

theorem integrand_not_integrable (t : ℝ) (ht : 0 < t) :
    ¬ Integrable (fun y => integrand t y) volume := by
  intro h
  have hfi : HasFiniteIntegral (fun y => integrand t y) volume := h.hasFiniteIntegral
  have hlt : ∫⁻ y, ENNReal.ofReal (integrand t y) ∂volume < ∞ := by
    refine (hasFiniteIntegral_iff_ofReal ?_).1 hfi
    filter_upwards with y
    exact le_of_lt (integrand_pos t ht y)
  have htop : ∫⁻ y, ENNReal.ofReal (integrand t y) ∂volume = ∞ :=
    integrand_lintegral_eq_top t ht
  rw [htop] at hlt
  exact lt_irrefl _ hlt

/-! ## 5. The main defect theorem -/

theorem integral_undef_zero (t : ℝ) (ht : 0 < t) :
    ∫ y, integrand t y ∂volume = 0 :=
  integral_undef (integrand_not_integrable t ht)

/-- **The D7 initial-condition field is false for the standard Euclidean heat kernel
on `ℝ`.**  The continuous test function `testFunction` makes the integrand
non-integrable for every `t > 0`, so the integral is identically `0` on the
neighbourhood `(0, ∞)` of `0` within `𝓝[>] 0`, and hence cannot converge to
`testFunction 0 = 1`. -/
theorem not_initialCondition_gaussian :
    ¬ D7InitialConditionAt gaussianKernelXY 0 := by
  intro h
  have htest := h testFunction testFunction_continuous
  have hz : (fun t : ℝ => ∫ y, gaussianKernelXY 0 y t * testFunction y ∂volume)
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ) := by
    simp only [EventuallyEq]
    rw [eventually_nhdsWithin_iff]
    filter_upwards with t ht
    have hInt := integral_undef_zero t ht
    simpa [integrand] using hInt
  have h0 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (testFunction 0)) :=
    htest.congr' hz
  have hzero : testFunction 0 = 0 :=
    tendsto_nhds_unique (f := fun _ : ℝ => (0 : ℝ)) (l := 𝓝[>] (0 : ℝ)) h0 tendsto_const_nhds
  rw [testFunction_zero] at hzero
  norm_num at hzero

/-- The stronger quantified form: the field fails for *some* continuous test
function, so no Gaussian heat-kernel datum on `ℝ` (with Lebesgue volume) can
certify the D7 `initialCondition` field. -/
theorem not_initialCondition_gaussian_quantified :
    ¬ (∀ (x : ℝ) (f : ℝ → ℝ), Continuous f →
      Tendsto (fun t : ℝ => ∫ y, gaussianKernelXY x y t * f y ∂volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x))) := by
  intro h
  exact not_initialCondition_gaussian (by
    intro f hf
    simpa using h 0 f hf)

end Poincare.D12.SemanticLedger
