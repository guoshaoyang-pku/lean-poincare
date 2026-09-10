import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Poincare.D7.Geodesic.Basic

**D7 geodesic / exponential-map layer: the model-space `GeodesicData` interface.**

This module is part of the `D7-geodesic-exponential` task. It works in the *model space* of a
normed `ℝ`-vector space `E`, where the geodesic equation is an explicit second-order ODE

  `γ'' (t) = Γ (γ t) (γ' t) (γ' t)`,

with `Γ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E` the (bundled, point-dependent) Christoffel symbol. This is exactly the
coordinate form of the geodesic equation, with the sign convention in which the classical
Christoffel symbol is `-Γ`. The sign is irrelevant for the three toy theorems proved here, and is
recorded so that the interface is unambiguous.

## Main definitions

* `FlatMetric E`: a base-point independent (`flat`) metric, i.e. a symmetric positive-definite
  continuous bilinear form.
* `IsMetricCompatible g Γ`: the metric-compatibility (metric-parallel) condition for the flat
  metric `g` and the connection `Γ`. For the covariant derivative `∇_X W = D_X W - Γ (X, W)`
  and a metric that is constant in the base point this is exactly
  `g (Γ x v w) u + g w (Γ x v u) = 0`.
* `IsGeodesic Γ γ`: `γ` solves the geodesic equation for `Γ`.
* `IsAffineGeodesic γ`: `γ` solves the geodesic equation of the *flat (affine) connection*
  `Γ = 0`; equivalently `γ'' = 0`.
* `GeodesicData E`: the explicit interface bundling connection, initial point, initial velocity
  and solution curve, with all hypotheses visible as structure fields.

## Honest boundary

Everything in this file is model-space (a single vector space, no manifold). The manifold-level
counterparts are *stated only* in `Poincare.D7.Geodesic.ManifoldInterfaces`, with the missing
mathlib dependencies listed there. All proofs are complete: no `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/

open scoped InnerProductSpace

namespace Poincare
namespace D7
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A flat metric.** A continuous bilinear form on the model space `E` which is symmetric and
positive definite. "Flat" means that the form does not depend on the base point, so that in the
metric-compatibility identity below the derivative of the metric itself drops out. -/
structure FlatMetric (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The metric as a continuous bilinear form. -/
  metric : E →L[ℝ] E →L[ℝ] ℝ
  /-- Symmetry of the metric. -/
  symm : ∀ v w : E, metric v w = metric w v
  /-- Positive definiteness of the metric. -/
  pos : ∀ v : E, v ≠ 0 → 0 < metric v v

/-- **Metric compatibility.** For the covariant derivative `∇_X W = D_X W - Γ (X, W)` on the model
space and a metric that is constant in the base point, metric compatibility
`X (g (W, U)) = g (∇_X W, U) + g (W, ∇_X U)` reduces to the pointwise condition
`g (Γ x v w) u + g w (Γ x v u) = 0` for all `x v w u`. -/
def IsMetricCompatible (g : FlatMetric E) (Γ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) : Prop :=
  ∀ x v w u : E, g.metric (Γ x v w) u + g.metric w (Γ x v u) = 0

/-- **The geodesic equation for a model-space connection `Γ`.** The curve `γ : ℝ → E` is a
geodesic when it is differentiable with derivative `deriv γ` and its derivative field satisfies
`(deriv γ)' t = Γ (γ t) (γ' t) (γ' t)`. Both regularity requirements are explicit. -/
def IsGeodesic (Γ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (γ : ℝ → E) : Prop :=
  (∀ t : ℝ, HasDerivAt γ (deriv γ t) t) ∧
    ∀ t : ℝ, HasDerivAt (deriv γ) (Γ (γ t) (deriv γ t) (deriv γ t)) t

/-- **The flat (affine) geodesic equation.** A curve is an affine geodesic when it is
differentiable with derivative `deriv γ` and that derivative is constant, i.e. `γ'' = 0`.
This is `IsGeodesic 0 γ`. -/
def IsAffineGeodesic (γ : ℝ → E) : Prop :=
  (∀ t : ℝ, HasDerivAt γ (deriv γ t) t) ∧ ∀ t : ℝ, HasDerivAt (deriv γ) 0 t

/-- **The flat connection is the zero connection.** -/
theorem isGeodesic_zero_iff {γ : ℝ → E} :
    IsGeodesic (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) γ ↔ IsAffineGeodesic γ := by
  simp [IsGeodesic, IsAffineGeodesic]

/-- The zero connection is compatible with any flat metric (both terms of the compatibility
condition vanish because `Γ = 0`). -/
theorem isMetricCompatible_zero (g : FlatMetric E) :
    IsMetricCompatible g (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := by
  intro x v w u
  simp

/-- **The `GeodesicData` interface.** It bundles

* a connection `Γ` (the Christoffel symbol of the model space),
* an initial point `p`,
* an initial velocity `v`,
* a solution curve `curve`,

together with the *visible* hypotheses that `curve` starts at `p`, has derivative `v` at time `0`,
and solves the geodesic equation for `Γ`. -/
structure GeodesicData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The connection (Christoffel symbol). -/
  Γ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E
  /-- The initial point. -/
  p : E
  /-- The initial velocity. -/
  v : E
  /-- The solution curve. -/
  curve : ℝ → E
  /-- The curve starts at the initial point. -/
  curve_zero : curve 0 = p
  /-- The initial velocity is the derivative at time `0`. -/
  deriv_curve_zero : deriv curve 0 = v
  /-- The curve solves the geodesic equation for the connection. -/
  isGeodesic : IsGeodesic Γ curve

namespace GeodesicData

variable (d : GeodesicData E)

/-- The curve of a `GeodesicData` is differentiable, with derivative `deriv curve`. -/
theorem hasDerivAt_curve (t : ℝ) : HasDerivAt d.curve (deriv d.curve t) t :=
  d.isGeodesic.1 t

/-- The derivative of the curve of a `GeodesicData` satisfies the geodesic equation. -/
theorem hasDerivAt_deriv_curve (t : ℝ) :
    HasDerivAt (deriv d.curve) (d.Γ (d.curve t) (deriv d.curve t) (deriv d.curve t)) t :=
  d.isGeodesic.2 t

end GeodesicData

end Geodesic
end D7
end Poincare
