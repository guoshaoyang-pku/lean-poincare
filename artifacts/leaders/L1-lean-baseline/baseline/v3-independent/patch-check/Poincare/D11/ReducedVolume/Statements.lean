import Poincare.D11.ReducedVolume.Volume
import Poincare.D11.ReducedVolume.StraightRays
import Poincare.D7.Reduced.Statements
import Poincare.D7.Reduced.Certificate
import Mathlib.LinearAlgebra.Determinant

/-!
# Poincare.D11.ReducedVolume.Statements

**D11 reduced volume, Euclidean case, part 4: the named propositions — the monotonicity
theorem and the manifold reduced-volume interface consumed by `D7-reduced-length-volume`.**

The D7 layer (`Poincare.D7.Reduced`) states the reduced-length / reduced-volume layer over a
metric-flow interface and records the general (manifold) analytic content as state-only
propositions: `LMinimizerExistence`, `JacobianComparison`, `ReducedVolumeMonotonicity`
(`Poincare.D7.Reduced.Statements`), and the certificate structure `ReducedVolumeCertificate`
(`Poincare.D7.Reduced.Certificate`).  This file connects the unconditional Euclidean
computation of `Poincare.D11.ReducedVolume` to that layer.

## What this file provides

* `ManifoldReducedVolumeInterface E` — **the manifold reduced-volume interface**: the D7
  metric-flow interface `flow : MetricFlowInterface E`, the dimension `n`, the reduced
  distance `ℓ(q, τ)`, and the reduced volume `Ṽ(τ)`.  These are exactly the data fields the
  D7 reduced-volume layer consumes.
* `ReducedVolumeMonotonicityTheorem M` — **the monotonicity theorem as a named `Prop`**:
  the reduced volume is nonincreasing on positive backward times.  State-only for the
  general interface; its general proof needs the ten D7 missing inputs
  `Poincare.D7.Reduced.reducedVolumeDependencies` (RLV-1 … RLV-10).
* `euclideanManifoldReducedVolumeInterface n` — **the Euclidean instantiation**, with one
  reference theorem per field (`..._flow`, `..._dimension`, `..._reducedDistance`,
  `..._reducedVolume`).
* `euclideanReducedVolumeCertificate n` — **the Euclidean instantiation of every field of
  the D7 `ReducedVolumeCertificate`**: `flow`, `volume`, `derivative`, `hasDerivAt_volume`,
  `derivative_nonpos`, `volume_nonneg`, each discharged by the Euclidean computation, with
  one reference theorem per field.
* `euclidean_reducedVolumeMonotonicity`, `euclidean_manifoldReducedVolumeMonotonicity` —
  **the monotonicity theorem, proved unconditionally in the Euclidean case** (with equality:
  the reduced volume is the constant `1`).
* `flatLExponential`, `flatLExponential_det` — the flat `L`-exponential `v ↦ 2√τ v` and its
  Jacobian `(2√τ)ⁿ`; `euclideanJacobianComparisonInterface`, `euclidean_jacobianComparison`
  — the Euclidean instantiation of the D7 `JacobianComparisonInterface` and the D7
  `JacobianComparison` `Prop`, holding **with equality** in flat space.
* `euclidean_manifold_LMinimizerExistence` — the D7 state-only `LMinimizerExistence` `Prop`,
  proved for the `flow` field of the Euclidean interface.
* `EuclideanReducedVolumeAnchor n` and `euclideanReducedVolumeAnchor` — the packaged
  conjunction of the four unconditional Euclidean anchors.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in this file; the
general monotonicity theorem is a `def ... : Prop` (a well-formed statement), never an axiom,
and it is **proved** for the Euclidean instantiation.

## Field-instantiation table (which fields the Euclidean computation fills in)

| consumed declaration (D7) | field | Euclidean value | discharged |
| --- | --- | --- | --- |
| `MetricFlowInterface` | `scalarCurvature` | `fun _ _ => 0` (flat, `R = 0`) | `euclideanFlow_scalarCurvature` |
| `MetricFlowInterface` | `metric` | `fun _ x y => ⟪x, y⟫` | `euclideanFlow_metric` |
| `ReducedVolumeCertificate` | `flow` | `euclideanFlow n` | `euclideanReducedVolumeCertificate_flow` |
| `ReducedVolumeCertificate` | `volume` | `fun τ => reducedVolume n τ` | `euclideanReducedVolumeCertificate_volume` |
| `ReducedVolumeCertificate` | `derivative` | `fun _ => 0` | `euclideanReducedVolumeCertificate_derivative` |
| `ReducedVolumeCertificate` | `hasDerivAt_volume` | constant-`1` derivative | proved in `euclideanReducedVolumeCertificate` |
| `ReducedVolumeCertificate` | `derivative_nonpos` | `0 ≤ 0` | proved in `euclideanReducedVolumeCertificate` |
| `ReducedVolumeCertificate` | `volume_nonneg` | `0 ≤ 1` | `reducedVolume_nonneg` |
| `JacobianComparisonInterface` | `jacobian` / `comparison` | `(2√τ)ⁿ` (flat `L`-exponential Jacobian) | `flatLExponential_det`, `euclidean_jacobianComparison` |
| `LMinimizerExistence` (state-only `Prop`) | — | straight rays | `euclidean_manifold_LMinimizerExistence` |
-/

open MeasureTheory intervalIntegral Real
open Poincare.D7.Reduced
open scoped RealInnerProductSpace Topology

namespace Poincare
namespace D11
namespace ReducedVolume

noncomputable section

/-! ## 1. The manifold reduced-volume interface and the monotonicity theorem -/

/-- **Manifold reduced-volume interface.**  The data consumed by the D7 reduced-length /
reduced-volume layer (`Poincare.D7.Reduced`): the metric-flow interface
(`flow : MetricFlowInterface E`), the dimension `n` of the `(4πτ)^(-n/2)` normalisation, the
reduced distance `ℓ(q, τ)` and the reduced volume `Ṽ(τ)`.  The Euclidean computation
instantiates every field in `euclideanManifoldReducedVolumeInterface`. -/
structure ManifoldReducedVolumeInterface (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  /-- The metric-flow interface field, consumed by `Poincare.D7.Reduced.MetricFlowInterface`. -/
  flow : MetricFlowInterface E
  /-- The dimension field `n` of the reduced-volume normalisation `(4πτ)^(-n/2)`. -/
  dimension : ℕ
  /-- The reduced-distance field `ℓ(q, τ)`. -/
  reducedDistance : ℝ → E → ℝ
  /-- The reduced-volume field `Ṽ(τ)`. -/
  reducedVolume : ℝ → ℝ

/-- **Monotonicity theorem (named `Prop`).**  The reduced volume of a manifold reduced-volume
interface is nonincreasing on positive backward times:

```
0 < τ₁ ≤ τ₂  ⇒  Ṽ(τ₂) ≤ Ṽ(τ₁).
```

This is the D7 declaration `Poincare.D7.Reduced.ReducedVolumeMonotonicity` instantiated at
the interface's volume functional.  It is **state-only** for the general (manifold)
interface: the general proof needs the ten missing inputs recorded in
`Poincare.D7.Reduced.reducedVolumeDependencies` (RLV-1 path space, RLV-2 `L`-geodesic
equation, RLV-3 minimiser regularity, RLV-4 `L`-exponential map, RLV-5 second variation,
RLV-6 Jacobian comparison, RLV-7 reduced-length differential inequality, RLV-8
differentiation under the integral, RLV-9 manifold metric flow, RLV-10 Gaussian
normalisation).  The Euclidean computation instantiates the interface
(`euclideanManifoldReducedVolumeInterface`) and **proves** the theorem unconditionally
(`euclidean_manifoldReducedVolumeMonotonicity`), with equality: the reduced volume is the
constant `1`. -/
def ReducedVolumeMonotonicityTheorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : ManifoldReducedVolumeInterface E) : Prop :=
  ReducedVolumeMonotonicity M.reducedVolume

/-- The named ledger of the D7 missing inputs on which the *general* monotonicity theorem
still depends; each entry is discharged in the Euclidean case by the computation of this
package. -/
def generalMonotonicityMissingDependencies : List String := [
  "RLV-1 path space",
  "RLV-2 L-geodesic equation",
  "RLV-3 minimiser regularity",
  "RLV-4 L-exponential map",
  "RLV-5 second variation and index form",
  "RLV-6 Jacobian comparison",
  "RLV-7 reduced-length differential inequality",
  "RLV-8 differentiation under the integral",
  "RLV-9 manifold metric flow",
  "RLV-10 Gaussian normalisation"
]

theorem generalMonotonicityMissingDependencies_ne_nil :
    generalMonotonicityMissingDependencies ≠ [] := by
  simp [generalMonotonicityMissingDependencies]

theorem generalMonotonicityMissingDependencies_length :
    generalMonotonicityMissingDependencies.length = 10 := rfl

/-! ## 2. The Euclidean instantiation of the manifold interface -/

/-- **The Euclidean instantiation of the manifold reduced-volume interface**: the flat flow,
dimension `n`, the heat-kernel reduced distance `ℓ(x,τ) = |x|²/(4τ)`, and the reduced volume
`Ṽ(τ) = 1`. -/
def euclideanManifoldReducedVolumeInterface (n : ℕ) :
    ManifoldReducedVolumeInterface (EuclideanSpace ℝ (Fin n)) where
  flow := euclideanFlow n
  dimension := n
  reducedDistance := fun τ x => heatKernelReducedDistance n τ x
  reducedVolume := fun τ => reducedVolume n τ

/-- **Field reference**: the Euclidean computation instantiates the `flow` field with the flat
metric-flow interface `euclideanFlow n` (zero scalar curvature, Euclidean metric). -/
theorem euclideanManifoldReducedVolumeInterface_flow (n : ℕ) :
    (euclideanManifoldReducedVolumeInterface n).flow = euclideanFlow n := rfl

/-- **Field reference**: the Euclidean computation instantiates the `dimension` field with the
dimension `n` of `ℝⁿ`. -/
theorem euclideanManifoldReducedVolumeInterface_dimension (n : ℕ) :
    (euclideanManifoldReducedVolumeInterface n).dimension = n := rfl

/-- **Field reference**: the Euclidean computation instantiates the `reducedDistance` field
with the heat-kernel-asymptotics reduced distance `ℓ(x, τ) = |x|²/(4τ)`. -/
theorem euclideanManifoldReducedVolumeInterface_reducedDistance (n : ℕ) :
    (euclideanManifoldReducedVolumeInterface n).reducedDistance =
      fun τ x => heatKernelReducedDistance n τ x := rfl

/-- **Field reference**: the Euclidean computation instantiates the `reducedVolume` field with
the reduced volume functional `τ ↦ Ṽ(τ) = 1`. -/
theorem euclideanManifoldReducedVolumeInterface_reducedVolume (n : ℕ) :
    (euclideanManifoldReducedVolumeInterface n).reducedVolume = fun τ => reducedVolume n τ := rfl

/-- **The monotonicity theorem, proved for the Euclidean instantiation.**  Since the reduced
volume is the constant `1` on `ℝⁿ` (`reducedVolume_eq_one`), the named monotonicity `Prop`
holds unconditionally, with equality.  This is the first unconditional anchor of the
`L`-geometry chain. -/
theorem euclidean_manifoldReducedVolumeMonotonicity (n : ℕ) :
    ReducedVolumeMonotonicityTheorem (euclideanManifoldReducedVolumeInterface n) := by
  unfold ReducedVolumeMonotonicityTheorem euclideanManifoldReducedVolumeInterface
    ReducedVolumeMonotonicity
  intro τ₁ hτ₁ τ₂ hτ₂ h
  simpa using show reducedVolume n τ₂ ≤ reducedVolume n τ₁ by
    rw [reducedVolume_eq_one hτ₂, reducedVolume_eq_one hτ₁]

/-! ## 3. The Euclidean instantiation of the D7 reduced-volume certificate -/

/-- **The Euclidean computation instantiates every field of the D7
`ReducedVolumeCertificate`** (`Poincare.D7.Reduced.Certificate`):

* `flow := euclideanFlow n` — the flat metric-flow interface;
* `volume := fun τ => reducedVolume n τ` — the reduced volume, constant `1`;
* `derivative := fun _ => 0` — the backward-time derivative of the constant;
* `hasDerivAt_volume` — differentiability at every positive backward time (the volume is
  `1` on a neighbourhood of every `τ > 0`, so the derivative is `0`);
* `derivative_nonpos` — `0 ≤ 0`;
* `volume_nonneg` — `0 ≤ 1` (`reducedVolume_nonneg`). -/
def euclideanReducedVolumeCertificate (n : ℕ) :
    ReducedVolumeCertificate (EuclideanSpace ℝ (Fin n)) where
  flow := euclideanFlow n
  volume := fun τ => reducedVolume n τ
  derivative := fun _ => 0
  hasDerivAt_volume := fun τ hτ => by
    have hcongr : (fun s : ℝ => reducedVolume n s) =ᶠ[𝓝 τ] fun _ : ℝ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hτ] with s hs
      exact reducedVolume_eq_one (n := n) hs
    exact (hasDerivAt_const τ (1 : ℝ)).congr_of_eventuallyEq hcongr
  derivative_nonpos := fun _ _ => le_rfl
  volume_nonneg := fun τ hτ => reducedVolume_nonneg hτ

/-- **Field reference**: the `flow` field of the Euclidean certificate. -/
theorem euclideanReducedVolumeCertificate_flow (n : ℕ) :
    (euclideanReducedVolumeCertificate n).flow = euclideanFlow n := rfl

/-- **Field reference**: the `volume` field of the Euclidean certificate is the reduced volume
functional. -/
theorem euclideanReducedVolumeCertificate_volume (n : ℕ) :
    (euclideanReducedVolumeCertificate n).volume = fun τ => reducedVolume n τ := rfl

/-- **Field reference**: the `derivative` field of the Euclidean certificate is identically
zero. -/
theorem euclideanReducedVolumeCertificate_derivative (n : ℕ) :
    (euclideanReducedVolumeCertificate n).derivative = fun _ => (0 : ℝ) := rfl

/-- The checked D7 consequence of the certificate fields: the Euclidean reduced volume is
nonincreasing on positive backward times (in fact constant). -/
theorem euclideanReducedVolumeCertificate_antitoneOn (n : ℕ) :
    AntitoneOn (fun τ => reducedVolume n τ) (Set.Ioi 0) :=
  (euclideanReducedVolumeCertificate n).antitoneOn

/-- **Monotonicity in the Euclidean case** (the D7 `ReducedVolumeMonotonicity` `Prop` for the
Euclidean volume functional), derived from the instantiated certificate fields. -/
theorem euclidean_reducedVolumeMonotonicity (n : ℕ) :
    ReducedVolumeMonotonicity (euclideanReducedVolume n) := by
  unfold ReducedVolumeMonotonicity euclideanReducedVolume
  exact (euclideanReducedVolumeCertificate n).antitoneOn

/-! ## 4. The Euclidean instantiation of the D7 Jacobian comparison -/

/-- **The flat `L`-exponential map** at backward time `τ`, based at the origin: the linear map
`v ↦ 2√τ v` sending a tangent vector to the endpoint `γ(τ) = 2√τ v` of the straight ray
`γ(σ) = 2√σ v`. -/
def flatLExponential (n : ℕ) (τ : ℝ) : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (2 * Real.sqrt τ) • LinearMap.id

/-- **The Jacobian of the flat `L`-exponential** is the constant `(2√τ)ⁿ`: the determinant of
the rescaling `v ↦ 2√τ v` in dimension `n`. -/
theorem flatLExponential_det (n : ℕ) (τ : ℝ) :
    LinearMap.det (flatLExponential n τ) = (2 * Real.sqrt τ) ^ n := by
  unfold flatLExponential
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one,
    Poincare.D10.HeatKernelEuclidean.finrank_euclideanSpace_fin]

/-- **The Euclidean instantiation of the D7 `JacobianComparisonInterface`.**  The `jacobian`
field is the constant Jacobian `(2√τ)ⁿ` of the flat `L`-exponential (`flatLExponential_det`),
and the `comparison` field is the Euclidean comparison Jacobian `(2√τ)ⁿ`: in flat space the
`L`-exponential Jacobian equals the Euclidean comparison Jacobian exactly, so the D7
`JacobianComparison` `Prop` holds **with equality**. -/
def euclideanJacobianComparisonInterface (n : ℕ) :
    JacobianComparisonInterface (EuclideanSpace ℝ (Fin n)) where
  flow := euclideanFlow n
  jacobian := fun τ _ => (2 * Real.sqrt τ) ^ n
  comparison := fun τ _ => (2 * Real.sqrt τ) ^ n
  jacobian_nonneg := fun τ _ _ =>
    pow_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg τ)) n
  comparison_pos := fun _ _ hτ =>
    pow_pos (mul_pos zero_lt_two (Real.sqrt_pos.2 hτ)) n

/-- **Field reference**: the `jacobian` field of the Euclidean Jacobian comparison interface
is the constant `(2√τ)ⁿ`. -/
theorem euclideanJacobianComparisonInterface_jacobian (n : ℕ) :
    (euclideanJacobianComparisonInterface n).jacobian = fun τ _ => (2 * Real.sqrt τ) ^ n := rfl

/-- **Field reference**: the `comparison` field of the Euclidean Jacobian comparison interface
is the Euclidean comparison Jacobian `(2√τ)ⁿ`. -/
theorem euclideanJacobianComparisonInterface_comparison (n : ℕ) :
    (euclideanJacobianComparisonInterface n).comparison = fun τ _ => (2 * Real.sqrt τ) ^ n := rfl

/-- **The D7 `JacobianComparison` `Prop` in the Euclidean case**, holding with equality: the
flat `L`-exponential Jacobian is exactly the Euclidean comparison Jacobian `(2√τ)ⁿ`. -/
theorem euclidean_jacobianComparison (n : ℕ) :
    JacobianComparison (euclideanJacobianComparisonInterface n) := by
  intro τ _ _
  exact le_rfl

/-! ## 5. The packaged Euclidean anchor -/

/-- The D7 state-only `LMinimizerExistence` `Prop`, proved for the `flow` field of the
Euclidean manifold interface (the minimisers are the straight rays). -/
theorem euclidean_manifold_LMinimizerExistence (n : ℕ) :
    LMinimizerExistence (euclideanManifoldReducedVolumeInterface n).flow 0 := by
  unfold euclideanManifoldReducedVolumeInterface
  exact euclidean_LMinimizerExistence n

/-- **The Euclidean reduced-volume anchor** (named `Prop`): the conjunction of the four
unconditional anchors proved on flat `ℝⁿ` — the reduced distance is `|x|²/(4τ)`, the
reduced-volume integrand coincides with the Gaussian, the reduced volume is constant `1`,
and the monotonicity theorem holds. -/
def EuclideanReducedVolumeAnchor (n : ℕ) : Prop :=
  (∀ (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)), 0 < τ →
      heatKernelReducedDistance n τ x = ‖x‖ ^ 2 / (4 * τ)) ∧
  (∀ (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)), 0 < τ →
      reducedVolumeIntegrand n τ x = Poincare.D10.HeatKernelEuclidean.gaussianKernel n τ x) ∧
  (∀ τ : ℝ, 0 < τ → reducedVolume n τ = 1) ∧
  ReducedVolumeMonotonicityTheorem (euclideanManifoldReducedVolumeInterface n)

/-- **The Euclidean reduced-volume anchor is proved unconditionally.** -/
theorem euclideanReducedVolumeAnchor (n : ℕ) : EuclideanReducedVolumeAnchor n := by
  constructor
  · intro τ x hτ
    exact heatKernelReducedDistance_eq hτ x
  · constructor
    · intro τ x hτ
      exact reducedVolumeIntegrand_eq_gaussianKernel hτ x
    · constructor
      · intro τ hτ
        exact reducedVolume_eq_one hτ
      · exact euclidean_manifoldReducedVolumeMonotonicity n

end

end ReducedVolume
end D11
end Poincare
