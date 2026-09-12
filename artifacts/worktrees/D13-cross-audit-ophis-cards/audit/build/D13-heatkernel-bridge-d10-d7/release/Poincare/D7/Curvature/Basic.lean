import Poincare.Longrun.Geometry.Contraction
import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Stage1.RiemannAdapter

/-!
# Poincare.D7.Curvature.Basic

**D7 Riemann curvature tensor layer, part 1: the data structure and the two tensors.**

This module is part of the `D7-riemann-curvature-tensor` task. It consumes the accepted D6
weekly release (`release/`) unchanged and adds only files under `Poincare/D7/Curvature/`.

## What mathlib (pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`) provides

The probe in `Poincare/D7/Curvature/Probe.lean` records the following checked facts:

* `CovariantDerivative` (Koszul connection), `CovariantDerivative.torsion`,
  `CovariantDerivative.IsLeviCivitaConnection`, `CovariantDerivative.leviCivitaConnection`,
  `CovariantDerivative.isMetricCompatible_leviCivitaConnection`,
  `CovariantDerivative.torsion_leviCivitaConnection_eq_zero`,
  `CovariantDerivative.IsLeviCivitaConnection.uniqueness` all exist and are reused;
* there is **no** `CovariantDerivative.curvature`, no Riemann tensor, no Ricci tensor and no
  scalar curvature declaration. `grep -ri curvature Mathlib/` on the pinned checkout returns a
  single hit, a docstring in `MeasureTheory/Measure/Doubling.lean`. Therefore the D7 layer
  cannot define the curvature *of a mathlib `CovariantDerivative`*; that missing construction is
  recorded as an explicit unproved `Prop` in `Poincare/D7/Curvature/Blocked.lean`.

## What this file provides

* `RiemannCurvatureData V ι`: a **metric-compatible torsion-free connection datum** on a
  finite-dimensional real vector space `V`:
  * `conn : AbstractConnection ℝ V` — the D2 abstract Koszul connection
    `∇_X Y`, carrying the abstract bracket and the torsion-free identity
    `∇_X Y - ∇_Y X = [X,Y]` (`Poincare.Longrun.Geometry.AbstractConnection`);
  * `metric : MetricData V ι` — the explicit finite-dimensional metric datum of D2: a
    symmetric positive-definite bilinear form `form` together with a chosen orthonormal basis
    indexed by a finite type `ι` (`[Fintype ι]`, `[DecidableEq ι]`), plus
    `[FiniteDimensional ℝ V]`;
  * `compatible` — the metric-compatibility identity
    `⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩ = 0`.
* `RiemannCurvatureData.curvature` — the **(1,3) Riemann curvature tensor**
  `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]}Z`. It is *not* redefined: it is the D2
  `AbstractConnection.curvature`, whose first-pair antisymmetry and first Bianchi identity are
  already kernel-checked in D2. Only the bundling with the metric datum is new.
* `RiemannCurvatureData.curvatureForm` — the **(0,4) Riemann curvature tensor**
  `R(X,Y,Z,W) = ⟨R(X,Y)Z, W⟩`, obtained by lowering the last index with the metric. It reuses
  the D2 `Poincare.Longrun.Geometry.curvatureForm` (definitionally equal, `curvatureForm_apply`).
* `RiemannCurvatureData.toCurvatureOperator` — the bridge into the D2 Stage1
  `Poincare.CurvatureAlgebra.CurvatureOperator`.
* Linearity of the (0,4) tensor in each of its four arguments (`curvatureForm_add₁` …
  `curvatureForm_smul₄`), which the symmetry and sectional-curvature proofs consume.
* `alternating_bilinear_apply` — the elementary algebra lemma for an alternating bilinear
  form: `B (a•X + b•Y) (c•X + d•Y) = (a*d - b*c) * B X Y`. Used for the GL(2) invariance of
  sectional curvature.

## Honest boundary

The connection is **abstract algebraic** (a bilinear `nabla` on a module), not a mathlib
`CovariantDerivative` on a smooth manifold, and the bracket is abstract data. The manifold-level
construction is blocked (see `Poincare/D7/Curvature/Blocked.lean`). All proofs are complete: no
`sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Poincare
namespace D7
namespace Curvature

universe v w

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **Metric-compatible torsion-free connection datum.**

Bundles the D2 abstract Koszul connection (which already carries torsion-freeness for its
abstract bracket) with the D2 explicit finite-dimensional metric datum and the
metric-compatibility identity. The finite-dimensionality is explicit both as the typeclass
`[FiniteDimensional ℝ V]` and as the orthonormal basis field of `MetricData`; index raising is
available through `MetricData.raiseIndex` (used in `Symmetries.lean`). -/
structure RiemannCurvatureData (V : Type v) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ι : Type w) [Fintype ι] [DecidableEq ι] where
  /-- The abstract Koszul connection `∇_X Y` (torsion-free for its bracket). -/
  conn : AbstractConnection ℝ V
  /-- The explicit finite-dimensional metric datum. -/
  metric : MetricData V ι
  /-- Metric compatibility: `⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩ = 0`. -/
  compatible : ∀ X Y Z : V,
    metric.form (conn.nabla X Y) Z + metric.form Y (conn.nabla X Z) = 0

namespace RiemannCurvatureData

variable (D : RiemannCurvatureData V ι)

/-! ## The (1,3) Riemann curvature tensor -/

/-- **The (1,3) Riemann curvature tensor** `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]}Z`.

This is the D2 `AbstractConnection.curvature` (not a redefinition); the first-pair
antisymmetry and the first Bianchi identity are proved in
`Poincare.Longrun.Geometry.ConnectionAdapter`. -/
noncomputable def curvature : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V :=
  D.conn.curvature

/-- Defining equation of the (1,3) tensor. -/
@[simp] theorem curvature_apply (X Y Z : V) :
    D.curvature X Y Z = D.conn.curvature X Y Z := rfl

/-- Defining equation of the (1,3) tensor in terms of the connection. -/
theorem curvature_apply_eq (X Y Z : V) :
    D.curvature X Y Z =
      D.conn.nabla X (D.conn.nabla Y Z) - D.conn.nabla Y (D.conn.nabla X Z) -
        D.conn.nabla (D.conn.lie.bracket X Y) Z :=
  rfl

/-! ## The (0,4) Riemann curvature tensor -/

/-- **The (0,4) Riemann curvature tensor** `R(X,Y,Z,W) = ⟨R(X,Y)Z, W⟩`, obtained by lowering
the last index with the metric. It reuses the D2
`Poincare.Longrun.Geometry.curvatureForm`. -/
noncomputable def curvatureForm (X Y Z W : V) : ℝ :=
  Poincare.Longrun.Geometry.curvatureForm D.metric D.conn.toCurvatureOperator X Y Z W

/-- Defining equation of the (0,4) tensor: `R(X,Y,Z,W) = ⟨R(X,Y)Z, W⟩`. -/
theorem curvatureForm_apply (X Y Z W : V) :
    D.curvatureForm X Y Z W = D.metric.form (D.curvature X Y Z) W := rfl

/-- The (0,4) tensor is the D2 metric-lowered curvature form of the (1,3) tensor. -/
theorem curvatureForm_eq_d2 (X Y Z W : V) :
    D.curvatureForm X Y Z W =
      Poincare.Longrun.Geometry.curvatureForm D.metric D.conn.toCurvatureOperator X Y Z W :=
  rfl

/-! ## Metric compatibility, restated -/

/-- Metric compatibility solved for the first term:
`⟨∇_X Y, Z⟩ = -⟨Y, ∇_X Z⟩`. -/
theorem compatible_apply (X Y Z : V) :
    D.metric.form (D.conn.nabla X Y) Z = - D.metric.form Y (D.conn.nabla X Z) := by
  have h := D.compatible X Y Z
  linarith

/-! ## Four-slot linearity of the (0,4) tensor

These are the linearity lemmas used by the symmetry and sectional-curvature layers. They are
`@[simp]` so that expanding a substituted argument such as `a • X + b • Y` is a `simp` call.
The `@[simp]` orientation is terminating: the sum/product moves from the argument position to
the outside. -/

@[simp] theorem curvatureForm_add₁ (X₁ X₂ Y Z W : V) :
    D.curvatureForm (X₁ + X₂) Y Z W =
      D.curvatureForm X₁ Y Z W + D.curvatureForm X₂ Y Z W := by
  simp only [curvatureForm_apply, map_add, LinearMap.add_apply]

@[simp] theorem curvatureForm_smul₁ (a : ℝ) (X Y Z W : V) :
    D.curvatureForm (a • X) Y Z W = a * D.curvatureForm X Y Z W := by
  simp only [curvatureForm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem curvatureForm_add₂ (X Y₁ Y₂ Z W : V) :
    D.curvatureForm X (Y₁ + Y₂) Z W =
      D.curvatureForm X Y₁ Z W + D.curvatureForm X Y₂ Z W := by
  simp only [curvatureForm_apply, map_add, LinearMap.add_apply]

@[simp] theorem curvatureForm_smul₂ (a : ℝ) (X Y Z W : V) :
    D.curvatureForm X (a • Y) Z W = a * D.curvatureForm X Y Z W := by
  simp only [curvatureForm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem curvatureForm_add₃ (X Y Z₁ Z₂ W : V) :
    D.curvatureForm X Y (Z₁ + Z₂) W =
      D.curvatureForm X Y Z₁ W + D.curvatureForm X Y Z₂ W := by
  simp only [curvatureForm_apply, map_add, LinearMap.add_apply]

@[simp] theorem curvatureForm_smul₃ (a : ℝ) (X Y Z W : V) :
    D.curvatureForm X Y (a • Z) W = a * D.curvatureForm X Y Z W := by
  simp only [curvatureForm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem curvatureForm_add₄ (X Y Z W₁ W₂ : V) :
    D.curvatureForm X Y Z (W₁ + W₂) =
      D.curvatureForm X Y Z W₁ + D.curvatureForm X Y Z W₂ := by
  simp only [curvatureForm_apply, map_add, LinearMap.add_apply]

@[simp] theorem curvatureForm_smul₄ (a : ℝ) (X Y Z W : V) :
    D.curvatureForm X Y Z (a • W) = a * D.curvatureForm X Y Z W := by
  simp only [curvatureForm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-! ## The bridge into the D2 Stage1 `CurvatureOperator` -/

/-- The (1,3) tensor packaged as a D2 Stage1 `CurvatureOperator`. -/
noncomputable def toCurvatureOperator : CurvatureOperator ℝ V :=
  D.conn.toCurvatureOperator

/-- The packaged operator evaluates to the (1,3) tensor. -/
@[simp] theorem toCurvatureOperator_apply (X Y Z : V) :
    D.toCurvatureOperator X Y Z = D.curvature X Y Z := rfl

end RiemannCurvatureData

/-! ## Non-vacuity of the datum

The structure is inhabited by the zero connection for any metric datum, and by the D2 mean
connection `∇_X Y = ½[X,Y]` for any bracket that is skew for the metric. The mean-connection
constructor is the non-trivial witness (the zero connection is the degenerate case). -/

namespace RiemannCurvatureData

/-- **The zero connection datum**: the trivial abstract connection is metric-compatible for
any metric datum. A compiled non-vacuity witness (its curvature is zero, see
`zero_curvature`); it does not assert that any geometric curvature vanishes. -/
noncomputable def zero (m : MetricData V ι) : RiemannCurvatureData V ι where
  conn := AbstractConnection.zero
  metric := m
  compatible := by
    intro X Y Z
    simp [AbstractConnection.zero]

/-- The curvature of the zero-connection datum is zero. -/
@[simp] theorem zero_curvature (m : MetricData V ι) (X Y Z : V) :
    (zero m).curvature X Y Z = 0 := by
  simp [zero, curvature, AbstractConnection.zero]

/-- The metric-lowered curvature of the zero-connection datum is zero. -/
@[simp] theorem zero_curvatureForm (m : MetricData V ι) (X Y Z W : V) :
    (zero m).curvatureForm X Y Z W = 0 := by
  rw [curvatureForm_apply, zero_curvature, map_zero, LinearMap.zero_apply]

/-- **The mean-connection datum**: for a bracket that is skew for the metric, the D2 mean
connection `∇_X Y = ½[X,Y]` is metric-compatible, hence a non-trivial inhabitant of
`RiemannCurvatureData`. -/
noncomputable def mean (m : MetricData V ι) (b : LieBracketData ℝ V)
    (hb : ∀ X Y Z : V, m.form (b.bracket X Y) Z + m.form Y (b.bracket X Z) = 0) :
    RiemannCurvatureData V ι where
  conn := meanConnection b
  metric := m
  compatible := (meanConnection_isMetricCompatible_iff m b).mpr hb

/-- The connection of the mean-connection datum is the D2 mean connection. -/
theorem mean_conn (m : MetricData V ι) (b : LieBracketData ℝ V)
    (hb : ∀ X Y Z : V, m.form (b.bracket X Y) Z + m.form Y (b.bracket X Z) = 0) :
    (mean m b hb).conn = meanConnection b := rfl

end RiemannCurvatureData

/-! ## Alternating bilinear forms -/

/-- **Elementary algebra of alternating bilinear forms.** If `B : V → V → ℝ` is additive and
homogeneous in each slot and alternating (`B x y = -B y x`), then
`B (a•X + b•Y) (c•X + d•Y) = (a*d - b*c) * B X Y`.

This is the algebraic engine behind the GL(2) invariance of sectional curvature and of the
Gram determinant. -/
theorem alternating_bilinear_apply
    (B : V → V → ℝ)
    (hadd₁ : ∀ x₁ x₂ y : V, B (x₁ + x₂) y = B x₁ y + B x₂ y)
    (hsmul₁ : ∀ (a : ℝ) (x y : V), B (a • x) y = a * B x y)
    (hadd₂ : ∀ x y₁ y₂ : V, B x (y₁ + y₂) = B x y₁ + B x y₂)
    (hsmul₂ : ∀ (a : ℝ) (x y : V), B x (a • y) = a * B x y)
    (hanti : ∀ x y : V, B x y = - B y x)
    (a b c d : ℝ) (X Y : V) :
    B (a • X + b • Y) (c • X + d • Y) = (a * d - b * c) * B X Y := by
  have hXX : B X X = 0 := by
    have h := hanti X X
    linarith
  have hYY : B Y Y = 0 := by
    have h := hanti Y Y
    linarith
  simp only [hadd₁, hsmul₁, hadd₂, hsmul₂, hXX, hYY, hanti Y X]
  ring

end Curvature
end D7
end Poincare
