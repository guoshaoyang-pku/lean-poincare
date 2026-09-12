import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Poincare.D7.Reduced.Basic

**D7 reduced length / reduced volume layer, part 1: the `L`-length functional over a stated
metric-flow interface.**

This module is part of the `D7-reduced-length-volume` task.  It consumes the accepted
`D7-hamilton-short-time` package (imported unchanged) and adds only files under
`Poincare/D7/Reduced/`.

Perelman's reduced length is defined from the **`L`-length** of a curve
`γ : [τ₁, τ₂] → M` in *backward time* `τ = t₀ - t`:

```
L(γ) = ∫_{τ₁}^{τ₂} √τ ( R(γ(τ)) + |γ'(τ)|²_g(τ) ) dτ,
```

and the reduced length of a point `q` at backward time `τ` is
`l(q, τ) = L(γ_min) / (2 √τ)`, where `γ_min` minimises `L` among curves from the base point to
`q`.  The reduced volume is the Gaussian-weighted volume
`Ṽ(τ) = ∫ (4 π τ)^{-n/2} e^{-l(q,τ)} dV(q)`.

The pinned mathlib has no manifold-level path space, no minimiser theory for a variational
problem, and no Ricci-flow path calculus.  This layer therefore works over a **stated
metric-flow interface** in a real inner product space `E` (the tangent-space model): the scalar
curvature and the metric are *data*, and every analytic property used is an explicit field or an
explicit hypothesis.  The interface is inhabited by the finite-dimensional Gaussian shrinking
soliton model in `Poincare.D7.Reduced.Gaussian`.

## What this file provides

* `MetricFlowInterface E` — the stated metric-flow interface: a scalar curvature function
  `R : ℝ → E → ℝ`, a metric `g : ℝ → E → E → ℝ` that is symmetric, nonnegative on the diagonal
  and bilinear in the first slot.
* `MetricFlowInterface.LIntegrand`, `LlengthAlong`, `Llength` — the `L`-length integrand and
  functional, in the form with an explicit velocity field and in the form using `deriv`.
* `MetricFlowInterface.reducedLengthAlong`, `reducedLength` — division by `2 √τ`.
* `LPath` — admissible path data for the `L`-length minimisation problem: the curve, its
  velocity, the endpoint constraints, continuity on `[0, τ]`, differentiability on `(0, τ)` and
  the interval-integrability hypotheses needed to compare integrals.  The hypotheses are fields,
  so a consumer must display them at every use site.
* `LPath.length`, `LPath.reducedLength` — the `L`-length and reduced length of an admissible
  path.
* `IsLMinimizer`, `ReducedLengthData` — the minimising property as a `Prop` and the packaged
  minimiser together with its reduced length.

## Honest boundary

The model is finite-dimensional and pointwise: `E` plays the role of a tangent space (or of a
model space identified with the manifold), and the metric and scalar curvature are abstract data.
No manifold, path space, or variational existence theorem is constructed.  Every proof in this
file is complete; there is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open MeasureTheory intervalIntegral
open scoped RealInnerProductSpace

namespace Poincare
namespace D7
namespace Reduced

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Stated metric-flow interface.**

The intended instantiation is the following finite-dimensional model of a Ricci flow in backward
time `τ`: `E` is the tangent-space model, `scalarCurvature τ x` is the scalar curvature `R` at
backward time `τ` and point `x`, and `metric τ` is the metric tensor `g(τ)` at `x`.  The metric is
assumed symmetric, nonnegative on the diagonal, and bilinear in the first slot; these are the only
algebraic properties used by the `L`-length layer.

No Ricci-flow equation, no smoothness in `τ` or `x`, and no curvature bound is built into the
structure.  Those are added as explicit hypotheses or certificate fields where a theorem needs
them. -/
structure MetricFlowInterface (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The scalar curvature `R(τ, x)`. -/
  scalarCurvature : ℝ → E → ℝ
  /-- The metric tensor `g(τ)` evaluated at a pair of tangent vectors. -/
  metric : ℝ → E → E → ℝ
  /-- Symmetry of the metric. -/
  metric_symm : ∀ (τ : ℝ) (x y : E), metric τ x y = metric τ y x
  /-- Nonnegativity of the metric on the diagonal. -/
  metric_self_nonneg : ∀ (τ : ℝ) (x : E), 0 ≤ metric τ x x
  /-- Additivity of the metric in the first slot. -/
  metric_add_left : ∀ (τ : ℝ) (x y z : E),
    metric τ (x + y) z = metric τ x z + metric τ y z
  /-- Homogeneity of the metric in the first slot. -/
  metric_smul_left : ∀ (τ : ℝ) (c : ℝ) (x y : E),
    metric τ (c • x) y = c * metric τ x y

namespace MetricFlowInterface

variable (F : MetricFlowInterface E)

/-- Additivity of the metric in the second slot, from symmetry. -/
theorem metric_add_right (τ : ℝ) (x y z : E) :
    F.metric τ x (y + z) = F.metric τ x y + F.metric τ x z := by
  rw [F.metric_symm, F.metric_add_left, F.metric_symm τ x y, F.metric_symm τ x z]

/-- Homogeneity of the metric in the second slot, from symmetry. -/
theorem metric_smul_right (τ : ℝ) (c : ℝ) (x y : E) :
    F.metric τ x (c • y) = c * F.metric τ x y := by
  rw [F.metric_symm, F.metric_smul_left, F.metric_symm τ x y]

/-- The **`L`-length integrand** at backward time `τ` along the curve `γ` with velocity `γ'`:
`√τ (R(γ τ) + g(τ)(γ' τ, γ' τ))`. -/
def LIntegrandAlong (γ γ' : ℝ → E) (τ : ℝ) : ℝ :=
  Real.sqrt τ * (F.scalarCurvature τ (γ τ) + F.metric τ (γ' τ) (γ' τ))

/-- The **`L`-length** of a curve with an explicit velocity field over `[τ₁, τ₂]`:

```
LlengthAlong F γ γ' τ₁ τ₂ = ∫_{τ₁}^{τ₂} √τ ( R(γ τ) + g(τ)(γ' τ, γ' τ) ) dτ.
```

This is a definition only: no integrability, smoothness or endpoint condition is asserted. -/
def LlengthAlong (γ γ' : ℝ → E) (τ₁ τ₂ : ℝ) : ℝ :=
  ∫ τ in τ₁..τ₂, F.LIntegrandAlong γ γ' τ

/-- The `L`-length integrand using the derivative of the curve. -/
def LIntegrand (γ : ℝ → E) (τ : ℝ) : ℝ :=
  F.LIntegrandAlong γ (deriv γ) τ

/-- The **`L`-length** of a curve over `[τ₁, τ₂]`, using the derivative of the curve. -/
def Llength (γ : ℝ → E) (τ₁ τ₂ : ℝ) : ℝ :=
  ∫ τ in τ₁..τ₂, F.LIntegrand γ τ

/-- If the explicit velocity field agrees with the derivative on the interval, the two
definitions of the `L`-length agree. -/
theorem Llength_eq_LlengthAlong (γ γ' : ℝ → E) {τ₁ τ₂ : ℝ}
    (h : ∀ τ ∈ Set.uIcc τ₁ τ₂, deriv γ τ = γ' τ) :
    F.Llength γ τ₁ τ₂ = F.LlengthAlong γ γ' τ₁ τ₂ := by
  unfold Llength LlengthAlong LIntegrand LIntegrandAlong
  exact intervalIntegral.integral_congr fun τ hτ => by rw [h τ hτ]

/-- **Reduced length along an explicit path**: the `L`-length over `[0, τ]` divided by
`2 √τ`. -/
def reducedLengthAlong (γ γ' : ℝ → E) (τ : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt τ)) * F.LlengthAlong γ γ' 0 τ

/-- **Reduced length along a curve**, using the derivative. -/
def reducedLength (γ : ℝ → E) (τ : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt τ)) * F.Llength γ 0 τ

/-- The `L`-length is nonnegative when the scalar curvature is nonnegative. -/
theorem LlengthAlong_nonneg (hR : ∀ (τ : ℝ) (x : E), 0 ≤ F.scalarCurvature τ x)
    (γ γ' : ℝ → E) {a b : ℝ} (hab : a ≤ b) : 0 ≤ F.LlengthAlong γ γ' a b := by
  unfold LlengthAlong LIntegrandAlong
  refine intervalIntegral.integral_nonneg hab fun τ _ => ?_
  have hsqrt : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hmetric : 0 ≤ F.metric τ (γ' τ) (γ' τ) := F.metric_self_nonneg τ (γ' τ)
  exact mul_nonneg hsqrt (add_nonneg (hR τ (γ τ)) hmetric)

/-- The reduced length along an explicit path is nonnegative when the scalar curvature is
nonnegative and the time is nonnegative. -/
theorem reducedLengthAlong_nonneg (hR : ∀ (τ : ℝ) (x : E), 0 ≤ F.scalarCurvature τ x)
    (γ γ' : ℝ → E) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ F.reducedLengthAlong γ γ' τ := by
  unfold reducedLengthAlong
  have hL : 0 ≤ F.LlengthAlong γ γ' 0 τ := F.LlengthAlong_nonneg hR γ γ' hτ
  have hden : 0 ≤ 1 / (2 * Real.sqrt τ) := by positivity
  exact mul_nonneg hden hL

end MetricFlowInterface

/-- **Admissible path data for the `L`-length minimisation problem** from `p` to `q` over the
backward-time interval `[0, τ]`.

The fields are exactly the hypotheses needed to compare `L`-lengths: the endpoint constraints,
continuity on the closed interval, differentiability on the open interval with the stated
velocity, and interval-integrability of the `L`-length energy density `√x g(x)(γ', γ')` and of
every metric cross term `g(x)(c, γ')`.  The minimiser itself is an admissible path, so the
minimising property below is a comparison among admissible paths only. -/
structure LPath (F : MetricFlowInterface E) (p q : E) (τ : ℝ) where
  /-- The curve. -/
  curve : ℝ → E
  /-- The velocity field of the curve. -/
  velocity : ℝ → E
  /-- The curve starts at `p`. -/
  curve_zero : curve 0 = p
  /-- The curve ends at `q` at backward time `τ`. -/
  curve_tau : curve τ = q
  /-- The curve is continuous on `[0, τ]`. -/
  continuous_curve : ContinuousOn curve (Set.Icc 0 τ)
  /-- The curve has the stated velocity on `(0, τ)`. -/
  hasDerivAt : ∀ x ∈ Set.Ioo 0 τ, HasDerivAt curve (velocity x) x
  /-- The `L`-length energy density is interval-integrable. -/
  integrable_energy : IntervalIntegrable
    (fun x => Real.sqrt x * F.metric x (velocity x) (velocity x)) volume 0 τ
  /-- Every metric cross term with the velocity is interval-integrable. -/
  integrable_cross : ∀ c : E,
    IntervalIntegrable (fun x => F.metric x c (velocity x)) volume 0 τ

namespace LPath

variable {F : MetricFlowInterface E} {p q : E} {τ : ℝ}

/-- The **`L`-length of an admissible path**. -/
def length (P : LPath F p q τ) : ℝ := F.LlengthAlong P.curve P.velocity 0 τ

/-- The **reduced length of an admissible path**: `L`-length divided by `2 √τ`. -/
def reducedLength (P : LPath F p q τ) : ℝ :=
  (1 / (2 * Real.sqrt τ)) * P.length

/-- The `L`-length of an admissible path is nonnegative when the scalar curvature is
nonnegative. -/
theorem length_nonneg (P : LPath F p q τ)
    (hR : ∀ (τ : ℝ) (x : E), 0 ≤ F.scalarCurvature τ x) (hτ : 0 ≤ τ) : 0 ≤ P.length :=
  F.LlengthAlong_nonneg hR P.curve P.velocity hτ

/-- The reduced length of an admissible path is nonnegative when the scalar curvature is
nonnegative and the time is nonnegative. -/
theorem reducedLength_nonneg (P : LPath F p q τ)
    (hR : ∀ (τ : ℝ) (x : E), 0 ≤ F.scalarCurvature τ x) (hτ : 0 ≤ τ) :
    0 ≤ P.reducedLength := by
  unfold reducedLength
  exact mul_nonneg (by positivity) (P.length_nonneg hR hτ)

end LPath

/-- **The minimising property** for an admissible path: its `L`-length is at most the `L`-length
of every other admissible path with the same endpoints and the same backward time. -/
def IsLMinimizer {F : MetricFlowInterface E} {p q : E} {τ : ℝ}
    (P : LPath F p q τ) : Prop :=
  ∀ Q : LPath F p q τ, P.length ≤ Q.length

/-- **Reduced length data**: an admissible path together with a proof that it minimises the
`L`-length among admissible paths.  This is the structure relative to which the reduced length is
computed; the minimising property is a field, never an axiom. -/
structure ReducedLengthData (F : MetricFlowInterface E) (p q : E) (τ : ℝ) where
  /-- The minimising admissible path. -/
  path : LPath F p q τ
  /-- The minimising property. -/
  isMinimizer : IsLMinimizer path

namespace ReducedLengthData

variable {F : MetricFlowInterface E} {p q : E} {τ : ℝ}

/-- The **reduced length** of the packaged minimiser. -/
def reducedLength (D : ReducedLengthData F p q τ) : ℝ := D.path.reducedLength

/-- The `L`-length of the packaged minimiser. -/
def length (D : ReducedLengthData F p q τ) : ℝ := D.path.length

/-- The reduced length of a packaged minimiser is nonnegative when the scalar curvature is
nonnegative. -/
theorem reducedLength_nonneg (D : ReducedLengthData F p q τ)
    (hR : ∀ (τ : ℝ) (x : E), 0 ≤ F.scalarCurvature τ x) (hτ : 0 ≤ τ) :
    0 ≤ D.reducedLength :=
  D.path.reducedLength_nonneg hR hτ

end ReducedLengthData

end

end Reduced
end D7
end Poincare
