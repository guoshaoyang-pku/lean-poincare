import Poincare.D10.HeatKernelEuclidean.Basic
import Poincare.D7.Reduced.Gaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Poincare.D11.ReducedVolume.Basic

**D11 reduced volume, Euclidean case, part 1: the flat metric-flow interface, the `L`-length
functional, and the reduced distance from the heat-kernel asymptotics.**

This module is part of the `D11-reduced-volume-euclidean` task: Perelman's reduced volume
computed explicitly on `ℝⁿ` (realised as `EuclideanSpace ℝ (Fin n)`), using the D10 heat kernel

```
K(n, τ, x) = (4 π τ) ^ (-n/2) * exp (-‖x‖² / (4 τ))
```

of `Poincare.D10.HeatKernelEuclidean` and the stated metric-flow interface
`MetricFlowInterface` of `Poincare.D7.Reduced.Basic`.

## What this file provides

* `euclideanFlow n` — the **flat metric-flow interface** on `ℝⁿ`: scalar curvature `R ≡ 0`
  (the `R = 0` flat case) and the Euclidean metric `g(τ) = ⟪·,·⟫`, definitionally the D7
  Gaussian shrinking soliton model `Poincare.D7.Reduced.gaussianFlow n`.
* `flatLIntegrand`, `flatLlength`, `flatReducedLength` — the **`L`-length functional
  `L(γ) = ∫ √τ (|γ'|² + R) dτ`** specialised to the flat case: the integrand
  `√τ * (0 + |γ'(τ)|²)`; the agreement theorem `flatLlength_eq_LlengthAlong` shows this is
  exactly the D7 interface `L`-length on `euclideanFlow`.
* `heatKernelReducedDistance n τ x` — the **reduced distance extracted from the heat-kernel
  asymptotics**: `ℓ(x, τ) = -log ((4πτ)^(n/2) K(n, τ, x))`, i.e. the function for which
  `K = (4πτ)^(-n/2) exp (-ℓ)`.
* `heatKernel_asymptotics` — the heat kernel written in reduced-distance form
  `(4πτ)^(-n/2) exp (-ℓ(x,τ)) = K(n,τ,x)` for `τ > 0`.
* `heatKernelReducedDistance_eq` — **the explicit value `ℓ(x, τ) = |x|² / (4 τ)`** for
  `τ > 0`, the first anchor of the `L`-geometry chain.
* `heatKernelReducedDistance_eq_reducedLength` — agreement with the variational reduced length
  of the D7 Gaussian model (`Poincare.D7.Reduced.Gaussian.gaussianReducedLengthData`), i.e. the
  heat-kernel-asymptotics reduced distance equals the `L`-length-minimiser reduced distance.

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

/-! ## 1. The flat metric-flow interface on `ℝⁿ` -/

/-- **The flat metric-flow interface on `ℝⁿ`** (`EuclideanSpace ℝ (Fin n)`): zero scalar
curvature (the `R = 0` flat case of the `L`-length integrand `√τ (|γ'|² + R)`) and the
Euclidean metric.  Definitionally the Gaussian shrinking soliton model
`Poincare.D7.Reduced.gaussianFlow n` of the D7 reduced layer, so every D7 theorem for that
model applies verbatim. -/
def euclideanFlow (n : ℕ) : MetricFlowInterface (EuclideanSpace ℝ (Fin n)) :=
  gaussianFlow n

/-- The scalar curvature of the flat interface is identically zero: `R = 0`. -/
@[simp] theorem euclideanFlow_scalarCurvature (n : ℕ) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (euclideanFlow n).scalarCurvature τ x = 0 := by
  simp [euclideanFlow]

/-- The metric of the flat interface is the Euclidean inner product. -/
@[simp] theorem euclideanFlow_metric (n : ℕ) (τ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    (euclideanFlow n).metric τ x y = ⟪x, y⟫ := by
  simp [euclideanFlow]

/-! ## 2. The `L`-length functional in the flat case -/

/-- The **flat `L`-length integrand**: `√τ * (0 + |γ'(τ)|²)`, the `R = 0` specialisation of
Perelman's integrand `√τ (R(γ(τ)) + |γ'(τ)|²_g(τ))`.  The curve slot `γ` is kept for interface
fidelity with `MetricFlowInterface.LIntegrandAlong`; in the flat case the scalar-curvature term
is the literal `0`, so the integrand does not depend on `γ`. -/
def flatLIntegrand (_γ γ' : ℝ → EuclideanSpace ℝ (Fin n)) (τ : ℝ) : ℝ :=
  Real.sqrt τ * (0 + ‖γ' τ‖ ^ 2)

/-- The **flat `L`-length**: `∫_{τ₁}^{τ₂} √τ (0 + |γ'(τ)|²) dτ`. -/
def flatLlength (γ γ' : ℝ → EuclideanSpace ℝ (Fin n)) (τ₁ τ₂ : ℝ) : ℝ :=
  ∫ τ in τ₁..τ₂, flatLIntegrand γ γ' τ

/-- **Agreement with the D7 interface.**  The flat `L`-length is exactly the `L`-length of the
`MetricFlowInterface` `euclideanFlow`, because `|γ'|² = ⟪γ', γ'⟫` and `R = 0`. -/
theorem flatLlength_eq_LlengthAlong (γ γ' : ℝ → EuclideanSpace ℝ (Fin n)) (τ₁ τ₂ : ℝ) :
    flatLlength γ γ' τ₁ τ₂ = (euclideanFlow n).LlengthAlong γ γ' τ₁ τ₂ := by
  unfold flatLlength MetricFlowInterface.LlengthAlong MetricFlowInterface.LIntegrandAlong
    flatLIntegrand
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [euclideanFlow_scalarCurvature, euclideanFlow_metric, zero_add, zero_add,
    ← real_inner_self_eq_norm_sq]

/-- The **flat reduced length along a curve**: the `L`-length over `[0, τ]` divided by
`2 √τ`. -/
def flatReducedLength (γ : ℝ → EuclideanSpace ℝ (Fin n)) (τ : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt τ)) * flatLlength γ (deriv γ) 0 τ

/-- Agreement of the flat reduced length with the interface reduced length. -/
theorem flatReducedLength_eq_reducedLength (γ : ℝ → EuclideanSpace ℝ (Fin n)) (τ : ℝ) :
    flatReducedLength γ τ = (euclideanFlow n).reducedLength γ τ := by
  unfold flatReducedLength MetricFlowInterface.reducedLength MetricFlowInterface.Llength
    MetricFlowInterface.LIntegrand
  rw [flatLlength_eq_LlengthAlong γ (deriv γ) 0 τ]
  unfold MetricFlowInterface.LlengthAlong
  rfl

/-! ## 3. The reduced distance from the heat-kernel asymptotics -/

/-- **The reduced distance extracted from the heat-kernel asymptotics.**  On `ℝⁿ` the D10 heat
kernel satisfies `K(n, τ, x) = (4πτ)^(-n/2) exp (-ℓ(x, τ))`; the reduced distance is the
function read off from this asymptotics:

```
ℓ(x, τ) = -log ((4πτ)^(n/2) K(n, τ, x)).
```

This is the definition of Perelman's reduced distance `l(q, τ)` adapted to the flat case: the
`L`-length minimiser / heat-kernel asymptotic identifies `ℓ` without any minimisation, and
`heatKernelReducedDistance_eq_reducedLength` shows it agrees with the variational reduced
length of the D7 Gaussian model. -/
def heatKernelReducedDistance (n : ℕ) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -Real.log ((4 * π * τ) ^ ((n : ℝ) / 2) *
    Poincare.D10.HeatKernelEuclidean.gaussianKernel n τ x)

/-- **Explicit value of the reduced distance**: `ℓ(x, τ) = |x|² / (4 τ)` for `τ > 0`. -/
theorem heatKernelReducedDistance_eq {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) :
    heatKernelReducedDistance n τ x = ‖x‖ ^ 2 / (4 * τ) := by
  unfold heatKernelReducedDistance Poincare.D10.HeatKernelEuclidean.gaussianKernel
  have hbase : 0 < 4 * π * τ := by positivity
  have hpow : (4 * π * τ) ^ ((n : ℝ) / 2) * (4 * π * τ) ^ (-(n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hbase, show (n : ℝ) / 2 + (-(n : ℝ) / 2) = 0 by ring, Real.rpow_zero]
  have harg : (4 * π * τ) ^ ((n : ℝ) / 2) *
      ((4 * π * τ) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * τ))) =
      Real.exp (-‖x‖ ^ 2 / (4 * τ)) := by
    rw [← mul_assoc, hpow, one_mul]
  rw [harg, Real.log_exp]
  ring

/-- **Heat-kernel asymptotics in reduced-distance form**: for `τ > 0`,
`(4πτ)^(-n/2) exp (-ℓ(x, τ)) = K(n, τ, x)`. -/
theorem heatKernel_asymptotics {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) :
    (4 * π * τ) ^ (-(n : ℝ) / 2) * Real.exp (-heatKernelReducedDistance n τ x) =
      Poincare.D10.HeatKernelEuclidean.gaussianKernel n τ x := by
  rw [heatKernelReducedDistance_eq hτ, Poincare.D10.HeatKernelEuclidean.gaussianKernel_apply]
  rw [show -(‖x‖ ^ 2 / (4 * τ)) = -‖x‖ ^ 2 / (4 * τ) by ring]

/-- The reduced distance is nonnegative at positive backward times. -/
theorem heatKernelReducedDistance_nonneg {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ heatKernelReducedDistance n τ x := by
  rw [heatKernelReducedDistance_eq hτ]
  positivity

/-- **Agreement with the variational reduced length.**  The heat-kernel-asymptotics reduced
distance equals the reduced length of the packaged `L`-length minimiser of the D7 Gaussian
model (`gaussianReducedLengthData`), i.e. both are `|x|² / (4 τ)`. -/
theorem heatKernelReducedDistance_eq_reducedLength (q : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hτ : 0 < τ) :
    heatKernelReducedDistance n τ q = (gaussianReducedLengthData (n := n) q hτ).reducedLength := by
  rw [heatKernelReducedDistance_eq hτ, gaussianReducedLengthData_reducedLength q hτ]

/-- The reduced distance of the origin is zero: `ℓ(0, τ) = 0`. -/
theorem heatKernelReducedDistance_zero {τ : ℝ} (hτ : 0 < τ) :
    heatKernelReducedDistance n τ 0 = 0 := by
  rw [heatKernelReducedDistance_eq hτ]
  simp

end

end ReducedVolume
end D11
end Poincare
