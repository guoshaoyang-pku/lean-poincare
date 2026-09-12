import Poincare.D11.ReducedVolume.Basic
import Poincare.D10.HeatKernelEuclidean.Mass

/-!
# Poincare.D11.ReducedVolume.Volume

**D11 reduced volume, Euclidean case, part 3: the reduced-volume integrand coincides with the
Gaussian, and the reduced volume is constant `1`.**

Perelman's reduced volume on `ℝⁿ` is the Gaussian-weighted volume

```
Ṽ(τ) = ∫ (4πτ)^(-n/2) exp (-ℓ(x, τ)) dx,
```

with `ℓ(x, τ) = |x|²/(4τ)` the reduced distance computed in
`Poincare.D11.ReducedVolume.Basic` (from the heat-kernel asymptotics) and matched to the
`L`-length minimiser in `Poincare.D11.ReducedVolume.StraightRays`.

## What this file proves (all unconditional, for every `τ > 0`)

* `reducedVolumeIntegrand_eq_gaussianKernel` — **the reduced-volume integrand coincides with
  the Gaussian**: `(4πτ)^(-n/2) exp (-ℓ(x,τ)) = K(n, τ, x)`, the D10 heat kernel
  `Poincare.D10.HeatKernelEuclidean.gaussianKernel`.
* `reducedVolumeIntegrandUnnormalized_eq_gaussianKernel` — the task-literal form
  `τ^(-n/2) exp (-ℓ(x,τ)) = (4π)^(n/2) · K(n, τ, x)`: the unnormalised integrand coincides
  with the Gaussian up to the universal constant `(4π)^(n/2)`.
* `integral_reducedVolumeIntegrandUnnormalized` — `∫ τ^(-n/2) exp(-ℓ) dx = (4π)^(n/2)`,
  **independent of `τ`** (constant for all backward times), proved with the D10 Gaussian
  toolbox (`gaussianKernel_integral`, total mass `1` of the heat kernel).
* `reducedVolume_eq_one` — **the reduced volume is constant `= 1` for all `τ > 0`**:
  `Ṽ(τ) = ∫ (4πτ)^(-n/2) exp(-ℓ) dx = 1`.
* `reducedVolume_constant`, `reducedVolume_nonneg`, `integral_reducedVolumeIntegrandUnnormalized_constant`
  — the constancy statements.
* `euclideanReducedVolume` — the named functional `τ ↦ Ṽ(τ)` consumed by the D7 certificate
  layer in `Poincare.D11.ReducedVolume.Statements`.

Every proof is complete; there is no `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` in this file.
-/

open MeasureTheory intervalIntegral Real
open Poincare.D7.Reduced
open scoped RealInnerProductSpace

namespace Poincare
namespace D11
namespace ReducedVolume

noncomputable section

variable {n : ℕ}

/-! ## 1. The reduced-volume integrand -/

/-- **The reduced-volume integrand** in Perelman's normalisation:
`(4πτ)^(-n/2) exp (-ℓ(x, τ))`, with the reduced distance from the heat-kernel asymptotics. -/
def reducedVolumeIntegrand (n : ℕ) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * π * τ) ^ (-(n : ℝ) / 2) * Real.exp (-heatKernelReducedDistance n τ x)

/-- **The unnormalised reduced-volume integrand** in Perelman's transport form:
`τ^(-n/2) exp (-ℓ(x, τ))`. -/
def reducedVolumeIntegrandUnnormalized (n : ℕ) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  τ ^ (-(n : ℝ) / 2) * Real.exp (-heatKernelReducedDistance n τ x)

/-- **The reduced volume** on `ℝⁿ`: `Ṽ(τ) = ∫ (4πτ)^(-n/2) exp (-ℓ(x,τ)) dx`. -/
def reducedVolume (n : ℕ) (τ : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin n), reducedVolumeIntegrand n τ x

/-- The named functional `τ ↦ Ṽ(τ)` consumed by the D7 reduced-volume certificate layer. -/
def euclideanReducedVolume (n : ℕ) (τ : ℝ) : ℝ :=
  reducedVolume n τ

/-- **The reduced-volume integrand coincides with the Gaussian**: for `τ > 0`,
`(4πτ)^(-n/2) exp (-ℓ(x,τ)) = K(n, τ, x)`, the D10 heat kernel. -/
theorem reducedVolumeIntegrand_eq_gaussianKernel {τ : ℝ} (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin n)) :
    reducedVolumeIntegrand n τ x = Poincare.D10.HeatKernelEuclidean.gaussianKernel n τ x := by
  unfold reducedVolumeIntegrand
  rw [heatKernelReducedDistance_eq hτ, Poincare.D10.HeatKernelEuclidean.gaussianKernel_apply]
  rw [show -(‖x‖ ^ 2 / (4 * τ)) = -‖x‖ ^ 2 / (4 * τ) by ring]

/-- **The unnormalised integrand in heat-kernel form**: for `τ > 0`,
`τ^(-n/2) exp (-ℓ(x,τ)) = τ^(-n/2) exp (-|x|²/(4τ))`. -/
theorem reducedVolumeIntegrandUnnormalized_eq {τ : ℝ} (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin n)) :
    reducedVolumeIntegrandUnnormalized n τ x =
      τ ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * τ)) := by
  unfold reducedVolumeIntegrandUnnormalized
  rw [heatKernelReducedDistance_eq hτ]
  rw [show -(‖x‖ ^ 2 / (4 * τ)) = -‖x‖ ^ 2 / (4 * τ) by ring]

/-- **The task-literal coincidence**: for `τ > 0` the unnormalised reduced-volume integrand
`τ^(-n/2) exp (-ℓ)` coincides with the Gaussian up to the universal constant `(4π)^(n/2)`:

```
τ^(-n/2) exp (-ℓ(x,τ)) = (4π)^(n/2) · K(n, τ, x).
``` -/
theorem reducedVolumeIntegrandUnnormalized_eq_gaussianKernel {τ : ℝ} (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin n)) :
    reducedVolumeIntegrandUnnormalized n τ x =
      (4 * π) ^ ((n : ℝ) / 2) * Poincare.D10.HeatKernelEuclidean.gaussianKernel n τ x := by
  unfold reducedVolumeIntegrandUnnormalized Poincare.D10.HeatKernelEuclidean.gaussianKernel
  rw [heatKernelReducedDistance_eq hτ]
  rw [show -(‖x‖ ^ 2 / (4 * τ)) = -‖x‖ ^ 2 / (4 * τ) by ring]
  have hbase : 0 < 4 * π := by positivity
  have hcoef : τ ^ (-(n : ℝ) / 2) = (4 * π) ^ ((n : ℝ) / 2) * (4 * π * τ) ^ (-(n : ℝ) / 2) := by
    have hmul : (4 * π * τ) ^ (-(n : ℝ) / 2) =
        (4 * π) ^ (-(n : ℝ) / 2) * τ ^ (-(n : ℝ) / 2) :=
      Real.mul_rpow (le_of_lt hbase) hτ.le
    rw [hmul, ← mul_assoc, ← Real.rpow_add hbase,
      show (n : ℝ) / 2 + (-(n : ℝ) / 2) = 0 by ring, Real.rpow_zero, one_mul]
  rw [hcoef]
  ring

/-! ## 2. The reduced volume is constant `1` -/

/-- **The unnormalised reduced volume**: `∫ τ^(-n/2) exp (-ℓ(x,τ)) dx = (4π)^(n/2)`, constant
in `τ`.  The proof is the D10 Gaussian toolbox: the integrand is `(4π)^(n/2)` times the heat
kernel, whose total mass is `1` (`gaussianKernel_integral`). -/
theorem integral_reducedVolumeIntegrandUnnormalized {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : EuclideanSpace ℝ (Fin n), reducedVolumeIntegrandUnnormalized n τ x =
      (4 * π) ^ ((n : ℝ) / 2) := by
  have hcongr := MeasureTheory.integral_congr_ae (μ := volume)
    (f := fun x => reducedVolumeIntegrandUnnormalized n τ x)
    (g := fun x => (4 * π) ^ ((n : ℝ) / 2) *
      Poincare.D10.HeatKernelEuclidean.gaussianKernel n τ x) (by
      filter_upwards with x
      exact reducedVolumeIntegrandUnnormalized_eq_gaussianKernel hτ x)
  rw [hcongr, MeasureTheory.integral_const_mul,
    Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral n hτ, mul_one]

/-- The unnormalised reduced volume is constant for all positive backward times. -/
theorem integral_reducedVolumeIntegrandUnnormalized_constant {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁)
    (h₂ : 0 < τ₂) :
    (∫ x : EuclideanSpace ℝ (Fin n), reducedVolumeIntegrandUnnormalized n τ₁ x) =
      ∫ x : EuclideanSpace ℝ (Fin n), reducedVolumeIntegrandUnnormalized n τ₂ x := by
  rw [integral_reducedVolumeIntegrandUnnormalized h₁, integral_reducedVolumeIntegrandUnnormalized h₂]

/-- **The reduced volume is constant `1` for every backward time `τ > 0`.**  This is the
Euclidean anchor of Perelman's reduced volume: `Ṽ(τ) = 1` unconditionally on flat `ℝⁿ`. -/
theorem reducedVolume_eq_one {τ : ℝ} (hτ : 0 < τ) : reducedVolume n τ = 1 := by
  unfold reducedVolume
  have hcongr := MeasureTheory.integral_congr_ae (μ := volume)
    (f := fun x => reducedVolumeIntegrand n τ x)
    (g := fun x => Poincare.D10.HeatKernelEuclidean.gaussianKernel n τ x) (by
      filter_upwards with x
      exact reducedVolumeIntegrand_eq_gaussianKernel hτ x)
  rw [hcongr, Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral n hτ]

/-- The named Euclidean reduced-volume functional is constant `1` on positive times. -/
theorem euclideanReducedVolume_eq_one {τ : ℝ} (hτ : 0 < τ) : euclideanReducedVolume n τ = 1 :=
  reducedVolume_eq_one hτ

/-- The reduced volume is constant: its value does not depend on the positive backward time. -/
theorem reducedVolume_constant {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h₂ : 0 < τ₂) :
    reducedVolume n τ₁ = reducedVolume n τ₂ := by
  rw [reducedVolume_eq_one h₁, reducedVolume_eq_one h₂]

/-- The reduced volume is nonnegative at positive backward times. -/
theorem reducedVolume_nonneg {τ : ℝ} (hτ : 0 < τ) : 0 ≤ reducedVolume n τ := by
  rw [reducedVolume_eq_one hτ]
  norm_num

end

end ReducedVolume
end D11
end Poincare
