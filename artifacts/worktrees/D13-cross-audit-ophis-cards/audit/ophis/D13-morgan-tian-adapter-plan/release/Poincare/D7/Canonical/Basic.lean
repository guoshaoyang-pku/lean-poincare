/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface, part 1: ε-approximations, the three model
interfaces and the canonical-neighborhood certificate.**

This module fixes the interface of Perelman's canonical neighborhood theorem over the two
accepted D7 layers:

* the **compactness layer** `Poincare.D7.Compactness` supplies `PointedMetricSpace` and the
  ε-isometry form of pointed Gromov–Hausdorff convergence `GHConvergenceData`;
* the **curvature layer** `Poincare.D7.Curvature` supplies the algebraic curvature datum
  `RiemannCurvatureData` with its sectional curvature `sectionalCurvature`.

## What this file provides

* `EpsilonApproximation ε X Y`: the one-step (single error scale) form of the ε-isometry
  definition used by `GHConvergenceData`, together with `refl`, `mono`, `comp` (error
  `ε₁ + 2 ε₂`) and the two checked bridges to the compactness layer,
  `ofGHConvergenceData` and `toGHConvergenceData`.
* `CylinderInterface`, `CapInterface`, `SphereInterface`: the metric interfaces of the three
  model spaces that occur in the canonical neighborhood classification — the round cylinder
  `S²(r) × ℝ`, a round cap and the round sphere `S³(r)`.  Each interface records the metric
  features consumed by the classification: the model scale `r`, a pair of points at the
  model's characteristic distance (`π r` for the cylinder cross-section and the sphere, `r`
  for the cap boundary), the diameter bound where the model is compact, and the scalar
  curvature normalization (`2/r²` for the cylinder, `6/r²` for the cap and the sphere).
* `EpsilonNeck`, `EpsilonCap`, `EpsilonSpherical`: the region data — the region is ε-close in
  the `EpsilonApproximation` sense to a model interface of the *same* scale `r`.
* `CurvatureScaleDatum r`: the curvature normalization over the D7 curvature layer: an
  algebraic `RiemannCurvatureData` with a nondegenerate plane whose sectional curvature is
  `1/r²`.  This is the curvature slot of the certificate; the manifold-level curvature of the
  region is not available (see `Statements.lean` for the named missing inputs).
* `MetricNoncollapsing κ r X`: the checkable metric shadow of κ-noncollapsing used by the
  certificate: two points at distance at least `κ r`.
* `CanonicalNeighborhoodCertificate ε κ r X`: the classification datum — a kind
  (`neck`/`cap`/`compactSpherical`) with the corresponding ε-model data, the curvature
  normalization and the metric noncollapsing witness.

Every unproved input is an explicit structure field or a `Prop` parameter; there is no
unproved hole, no extra logical postulate, no kernel bypass, no native evaluation and no
statement stub in this file.
-/

import Poincare.D7.Compactness.Basic
import Poincare.D7.Curvature.Sectional

set_option autoImplicit false

open Filter Set Topology
open scoped Topology

namespace Poincare
namespace D7
namespace Canonical

universe u v w

open Poincare.D7.Compactness
open Poincare.D7.Curvature

noncomputable section

/-! ## 1. One-step ε-approximations over the compactness layer -/

/-- **A one-step pointed ε-approximation.**  `EpsilonApproximation ε X Y` records that the
pointed spaces `X` and `Y` are ε-close in the ε-isometry sense: a map `approx : X → Y` with
distortion at most `ε`, almost surjectivity up to `ε`, and basepoint error at most `ε`.

This is the single-scale version of `Poincare.D7.Compactness.GHConvergenceData`, which
controls a whole family of scales along a filter.  The two directions are bridged below by
`EpsilonApproximation.ofGHConvergenceData` and `EpsilonApproximation.toGHConvergenceData`. -/
structure EpsilonApproximation (ε : ℝ) (X Y : PointedMetricSpace.{u}) where
  /-- The error scale is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- The almost isometric approximation map. -/
  approx : X → Y
  /-- The distortion bound defining an ε-isometry. -/
  distortion : ∀ x y : X, |dist (approx x) (approx y) - dist x y| ≤ ε
  /-- Almost surjectivity of the approximation map. -/
  surjective : ∀ y : Y, ∃ x : X, dist y (approx x) ≤ ε
  /-- The approximation map moves basepoints by at most the error scale. -/
  base_dist : dist (approx X.base) Y.base ≤ ε

namespace EpsilonApproximation

variable {ε ε₁ ε₂ ε' : ℝ} {X Y Z : PointedMetricSpace.{u}}

/-- **Upper distortion bound.** -/
theorem dist_approx_le (A : EpsilonApproximation ε X Y) (x y : X) :
    dist (A.approx x) (A.approx y) ≤ dist x y + ε := by
  have h := (abs_le.mp (A.distortion x y)).2
  linarith

/-- **Lower distortion bound.** -/
theorem dist_le_dist_approx (A : EpsilonApproximation ε X Y) (x y : X) :
    dist x y ≤ dist (A.approx x) (A.approx y) + ε := by
  have h := (abs_le.mp (A.distortion x y)).1
  linarith

/-- **Reflexivity.**  Every pointed space is ε-close to itself for every `ε ≥ 0`. -/
def refl (X : PointedMetricSpace.{u}) (hε : 0 ≤ ε) : EpsilonApproximation ε X X where
  ε_nonneg := hε
  approx := id
  distortion := by
    intro x y
    simpa using hε
  surjective := by
    intro y
    exact ⟨y, by simpa using hε⟩
  base_dist := by
    simpa using hε

/-- **Monotonicity in the error scale.** -/
def mono (A : EpsilonApproximation ε X Y) (h : ε ≤ ε') : EpsilonApproximation ε' X Y where
  ε_nonneg := le_trans A.ε_nonneg h
  approx := A.approx
  distortion := fun x y => le_trans (A.distortion x y) h
  surjective := by
    intro y
    obtain ⟨x, hx⟩ := A.surjective y
    exact ⟨x, le_trans hx h⟩
  base_dist := le_trans A.base_dist h

/-- **Composition of one-step approximations.**  Two ε-approximations compose to an
`(ε₁ + 2 ε₂)`-approximation; the factor `2` accounts for the second distortion bound being
used once for surjectivity and once for the basepoint.  This is the one-step analogue of
`GHConvergenceData.comp`. -/
def comp (A₂ : EpsilonApproximation ε₂ Y Z) (A₁ : EpsilonApproximation ε₁ X Y) :
    EpsilonApproximation (ε₁ + 2 * ε₂) X Z where
  ε_nonneg := by
    have h₁ := A₁.ε_nonneg
    have h₂ := A₂.ε_nonneg
    linarith
  approx := fun x => A₂.approx (A₁.approx x)
  distortion := by
    intro x y
    have h₁ := A₁.dist_le_dist_approx x y
    have h₁' := A₁.dist_approx_le x y
    have h₂ := A₂.dist_approx_le (A₁.approx x) (A₁.approx y)
    have h₂' := A₂.dist_le_dist_approx (A₁.approx x) (A₁.approx y)
    rw [abs_le]
    constructor <;> linarith
  surjective := by
    intro z
    obtain ⟨y, hy⟩ := A₂.surjective z
    obtain ⟨x, hx⟩ := A₁.surjective y
    refine ⟨x, ?_⟩
    have h₂ := A₂.dist_approx_le y (A₁.approx x)
    calc dist z (A₂.approx (A₁.approx x))
        ≤ dist z (A₂.approx y) + dist (A₂.approx y) (A₂.approx (A₁.approx x)) :=
          dist_triangle _ _ _
      _ ≤ ε₂ + (dist y (A₁.approx x) + ε₂) := by linarith
      _ ≤ ε₂ + (ε₁ + ε₂) := by linarith
      _ = ε₁ + 2 * ε₂ := by ring
  base_dist := by
    have h₁ := A₁.base_dist
    have h₂ := A₂.dist_approx_le (A₁.approx X.base) Y.base
    have h₃ := A₂.base_dist
    calc dist (A₂.approx (A₁.approx X.base)) Z.base
        ≤ dist (A₂.approx (A₁.approx X.base)) (A₂.approx Y.base)
            + dist (A₂.approx Y.base) Z.base := dist_triangle _ _ _
      _ ≤ (dist (A₁.approx X.base) Y.base + ε₂) + ε₂ := by linarith
      _ ≤ (ε₁ + ε₂) + ε₂ := by linarith
      _ = ε₁ + 2 * ε₂ := by ring

/-! ### Bridges to the compactness layer -/

/-- **From GH convergence data to a one-step approximation.**  The approximation datum at a
single index `i` of a `GHConvergenceData` is an `EpsilonApproximation` with error `D.ε i`. -/
def ofGHConvergenceData {ι : Type v} {l : Filter ι} {X : ι → PointedMetricSpace.{u}}
    {Y : PointedMetricSpace.{u}} (D : GHConvergenceData l X Y) (i : ι) :
    EpsilonApproximation (D.ε i) (X i) Y where
  ε_nonneg := D.ε_nonneg i
  approx := D.approx i
  distortion := D.distortion i
  surjective := D.surjective i
  base_dist := D.base_dist i

/-- **From a sequence of one-step approximations to GH convergence data.**  A family of
`ε n`-approximations with `ε n → 0` is exactly pointed GH convergence along `atTop` in the
sense of the compactness layer. -/
def toGHConvergenceData {X : ℕ → PointedMetricSpace.{u}} {Y : PointedMetricSpace.{u}}
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (h0 : Tendsto ε atTop (𝓝 0))
    (A : ∀ n, EpsilonApproximation (ε n) (X n) Y) : GHConvergenceData atTop X Y where
  ε := ε
  ε_nonneg := hε
  ε_tendsto := h0
  approx := fun n => (A n).approx
  distortion := fun n => (A n).distortion
  surjective := fun n => (A n).surjective
  base_dist := fun n => (A n).base_dist

/-- **Round trip: GH data gives one-step data at every index, and back.**  The two bridges of
this section are inverse on a family of one-step approximations with a vanishing scale. -/
theorem toGHConvergenceData_ofGHConvergenceData {X : ℕ → PointedMetricSpace.{u}}
    {Y : PointedMetricSpace.{u}} (D : GHConvergenceData atTop X Y) :
    toGHConvergenceData D.ε D.ε_nonneg D.ε_tendsto
        (fun n => ofGHConvergenceData D n) = D := rfl

end EpsilonApproximation

/-! ## 2. The model interfaces -/

/-- **Interface of a round cylinder model `S²(r) × ℝ`.**  The metric features consumed by the
canonical-neighborhood classification: the scale `r > 0`, an isometric axis `ℝ → X` through
the basepoint (the `ℝ` factor), a pair of points at the cross-section diameter `π r` (the
antipodal points of `S²(r)` at the same axis parameter), and the scalar curvature
normalization `2/r²` of the round cylinder.

The interface does **not** assert that `space` is the smooth round cylinder; that
construction is a named missing input (`Statements.lean`). -/
structure CylinderInterface where
  /-- The model pointed space. -/
  space : PointedMetricSpace.{u}
  /-- The cross-section radius. -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- The axis of the cylinder (the `ℝ` factor). -/
  axis : ℝ → space
  /-- The basepoint is the axis point at parameter `0`. -/
  axis_base : axis 0 = space.base
  /-- The axis is unit speed. -/
  axis_dist : ∀ s t : ℝ, dist (axis s) (axis t) = |s - t|
  /-- A point antipodal to the basepoint in the cross-section. -/
  antipodal : space
  /-- The cross-section diameter is `π r`. -/
  antipodal_dist : dist space.base antipodal = Real.pi * radius
  /-- The scalar curvature of the model. -/
  scalarCurvature : ℝ
  /-- The scalar curvature normalization `2/r²`. -/
  scalarCurvature_eq : scalarCurvature = 2 / radius ^ 2

/-- **Interface of a round cap model.**  The metric features consumed by the classification:
the scale `r > 0`, a boundary point at distance exactly `r` from the basepoint (the boundary
sphere of the cap), the diameter bound `π r` of a round cap, and the scalar curvature
normalization `6/r²` of a piece of `S³(r)`.

The interface does **not** assert that `space` is a smooth round cap. -/
structure CapInterface where
  /-- The model pointed space. -/
  space : PointedMetricSpace.{u}
  /-- The cap radius. -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- A point on the boundary sphere of the cap. -/
  boundary : space
  /-- The boundary is at distance the cap radius from the basepoint. -/
  boundary_dist : dist space.base boundary = radius
  /-- The cap fits in a ball of radius `π r` (its diameter bound). -/
  diameter_le : ∀ x y : space, dist x y ≤ Real.pi * radius
  /-- The scalar curvature of the model. -/
  scalarCurvature : ℝ
  /-- The scalar curvature normalization `6/r²`. -/
  scalarCurvature_eq : scalarCurvature = 6 / radius ^ 2

/-- **Interface of a round sphere model `S³(r)`.**  The metric features consumed by the
classification: the scale `r > 0`, a pair of antipodal points at distance `π r`, the diameter
bound `π r`, and the scalar curvature normalization `6/r²`.

The interface does **not** assert that `space` is the smooth round sphere. -/
structure SphereInterface where
  /-- The model pointed space. -/
  space : PointedMetricSpace.{u}
  /-- The sphere radius. -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- A point antipodal to the basepoint. -/
  antipodal : space
  /-- Antipodal points are at distance `π r`. -/
  antipodal_dist : dist space.base antipodal = Real.pi * radius
  /-- The sphere has diameter `π r`. -/
  diameter_le : ∀ x y : space, dist x y ≤ Real.pi * radius
  /-- The scalar curvature of the model. -/
  scalarCurvature : ℝ
  /-- The scalar curvature normalization `6/r²`. -/
  scalarCurvature_eq : scalarCurvature = 6 / radius ^ 2

/-! ## 3. The three region data -/

/-- **An ε-neck at scale `r`.**  The region `X` is ε-close, in the one-step GH sense of
`EpsilonApproximation`, to a cylinder interface of radius exactly `r`. -/
structure EpsilonNeck (ε r : ℝ) (X : PointedMetricSpace.{u}) where
  /-- The round-cylinder model. -/
  model : CylinderInterface.{u}
  /-- The model radius is the certificate scale. -/
  radius_eq : model.radius = r
  /-- The region is ε-close to the model. -/
  approx : EpsilonApproximation ε X model.space

/-- **An ε-cap at scale `r`.**  The region `X` is ε-close to a cap interface of radius `r`. -/
structure EpsilonCap (ε r : ℝ) (X : PointedMetricSpace.{u}) where
  /-- The round-cap model. -/
  model : CapInterface.{u}
  /-- The model radius is the certificate scale. -/
  radius_eq : model.radius = r
  /-- The region is ε-close to the model. -/
  approx : EpsilonApproximation ε X model.space

/-- **An ε-compact-spherical region at scale `r`.**  The region `X` is ε-close to a sphere
interface of radius `r`. -/
structure EpsilonSpherical (ε r : ℝ) (X : PointedMetricSpace.{u}) where
  /-- The round-sphere model. -/
  model : SphereInterface.{u}
  /-- The model radius is the certificate scale. -/
  radius_eq : model.radius = r
  /-- The region is ε-close to the model. -/
  approx : EpsilonApproximation ε X model.space

namespace EpsilonNeck

variable {ε r : ℝ} {X : PointedMetricSpace.{u}}

/-- The model's antipodal distance, expressed at the certificate scale `r`. -/
theorem antipodal_dist (N : EpsilonNeck ε r X) :
    dist N.model.space.base N.model.antipodal = Real.pi * r := by
  rw [N.model.antipodal_dist, N.radius_eq]

/-- The scale is positive. -/
theorem radius_pos (N : EpsilonNeck ε r X) : 0 < r := by
  rw [← N.radius_eq]
  exact N.model.radius_pos

/-- **A sequence of ε-necks with vanishing error GH-converges to the cylinder.**  If every
region `X n` is an `ε n`-neck around the *same* cylinder interface `C` (the hypothesis
`hmodel` identifies the models), and `ε n → 0`, then the regions pointed-GH-converge to the
model `C.space` in the checked sense of the compactness layer.  This is the bridge that makes
the neck data a fixed-model convergence statement. -/
def toGHConvergenceData {X : ℕ → PointedMetricSpace.{u}} {ε : ℕ → ℝ}
    (C : CylinderInterface.{u}) (hε : ∀ n, 0 ≤ ε n) (h0 : Tendsto ε atTop (𝓝 0))
    (N : ∀ n, EpsilonNeck (ε n) C.radius (X n)) (hmodel : ∀ n, (N n).model = C) :
    GHConvergenceData atTop X C.space :=
  EpsilonApproximation.toGHConvergenceData ε hε h0
    (fun n => (hmodel n) ▸ (N n).approx)

end EpsilonNeck

namespace EpsilonCap

variable {ε r : ℝ} {X : PointedMetricSpace.{u}}

/-- The model's boundary distance, expressed at the certificate scale `r`. -/
theorem boundary_dist (C : EpsilonCap ε r X) :
    dist C.model.space.base C.model.boundary = r := by
  rw [C.model.boundary_dist, C.radius_eq]

/-- The scale is positive. -/
theorem radius_pos (C : EpsilonCap ε r X) : 0 < r := by
  rw [← C.radius_eq]
  exact C.model.radius_pos

end EpsilonCap

namespace EpsilonSpherical

variable {ε r : ℝ} {X : PointedMetricSpace.{u}}

/-- The model's antipodal distance, expressed at the certificate scale `r`. -/
theorem antipodal_dist (S : EpsilonSpherical ε r X) :
    dist S.model.space.base S.model.antipodal = Real.pi * r := by
  rw [S.model.antipodal_dist, S.radius_eq]

/-- The scale is positive. -/
theorem radius_pos (S : EpsilonSpherical ε r X) : 0 < r := by
  rw [← S.radius_eq]
  exact S.model.radius_pos

end EpsilonSpherical

/-! ## 4. The curvature normalization over the D7 curvature layer -/

/-- **Curvature normalization at scale `r`.**  An algebraic curvature datum of the D7
curvature layer with a nondegenerate plane whose sectional curvature is exactly `1/r²`.  This
is the curvature slot of `CanonicalNeighborhoodCertificate`: since the pinned mathlib has no
Riemann curvature tensor on a manifold, the normalization of the model scale is carried by an
explicit algebraic `RiemannCurvatureData` rather than by the region itself. -/
structure CurvatureScaleDatum (r : ℝ) where
  /-- The carrier of the algebraic curvature model. -/
  V : Type u
  /-- The additive group structure. -/
  [inst₁ : AddCommGroup V]
  /-- The real module structure. -/
  [inst₂ : Module ℝ V]
  /-- Finite-dimensionality. -/
  [inst₃ : FiniteDimensional ℝ V]
  /-- The index type of the orthonormal basis. -/
  ι : Type w
  /-- The finite index type. -/
  [inst₄ : Fintype ι]
  /-- Decidable equality on the index type. -/
  [inst₅ : DecidableEq ι]
  /-- The metric-compatible torsion-free connection datum. -/
  data : RiemannCurvatureData V ι
  /-- The first vector spanning the normalization plane. -/
  planeX : V
  /-- The second vector spanning the normalization plane. -/
  planeY : V
  /-- The normalization plane is nondegenerate. -/
  nondegenerate : data.IsNondegenerate2Plane planeX planeY
  /-- The sectional curvature realizes the scale: `sec = 1/r²`. -/
  sectional_eq : data.sectionalCurvature planeX planeY = 1 / r ^ 2

/-! ## 5. The metric shadow of noncollapsing -/

/-- **Metric noncollapsing at scale `r` with constant `κ`.**  The region contains a pair of
points at distance at least `κ r`.  This is the checkable metric consequence of Perelman's
κ-noncollapsing hypothesis used by the classification toy; the full volume noncollapsing
theorem over the D7 κ layer is a named missing input in `Statements.lean`. -/
structure MetricNoncollapsing (κ r : ℝ) (X : PointedMetricSpace.{u}) where
  /-- The noncollapsing constant is positive. -/
  κ_pos : 0 < κ
  /-- The far point witnessing the metric size of the region. -/
  farPoint : X
  /-- The region has metric size at least `κ r`. -/
  far_dist : κ * r ≤ dist X.base farPoint

/-! ## 6. The canonical-neighborhood certificate -/

/-- **The three alternatives of Perelman's canonical neighborhood classification.** -/
inductive CanonicalKind where
  /-- An ε-neck: a region ε-close to a round cylinder. -/
  | neck
  /-- An ε-cap: a region ε-close to a round cap. -/
  | cap
  /-- A compact ε-spherical region: a region ε-close to a round sphere. -/
  | compactSpherical
  deriving DecidableEq, Repr, Inhabited

/-- **Canonical-neighborhood certificate at scale `r`.**  The region `X` carries one of the
three canonical alternatives at scale `r`, together with the curvature normalization over the
D7 curvature layer and the metric noncollapsing witness.

* `kind` selects the alternative;
* `neck_data`, `cap_data`, `spherical_data` supply the corresponding ε-model data — the
  fields are indexed by the kind, so exactly one of them is consumed;
* `curvature` is the algebraic curvature normalization `sec = 1/r²`;
* `noncollapsing` is the metric shadow of κ-noncollapsing.

The certificate is a structure of data, never an assertion that any particular manifold
satisfies the hypotheses of the canonical neighborhood theorem. -/
structure CanonicalNeighborhoodCertificate (ε κ r : ℝ) (X : PointedMetricSpace.{u}) where
  /-- The certificate scale is positive. -/
  scale_pos : 0 < r
  /-- The selected canonical alternative. -/
  kind : CanonicalKind
  /-- The ε-neck data, when the neck alternative is selected. -/
  neck_data : kind = CanonicalKind.neck → EpsilonNeck ε r X
  /-- The ε-cap data, when the cap alternative is selected. -/
  cap_data : kind = CanonicalKind.cap → EpsilonCap ε r X
  /-- The ε-spherical data, when the compact-spherical alternative is selected. -/
  spherical_data : kind = CanonicalKind.compactSpherical → EpsilonSpherical ε r X
  /-- The curvature normalization over the D7 curvature layer. -/
  curvature : CurvatureScaleDatum r
  /-- The metric shadow of κ-noncollapsing. -/
  noncollapsing : MetricNoncollapsing κ r X

namespace CanonicalNeighborhoodCertificate

variable {ε κ r : ℝ} {X : PointedMetricSpace.{u}}

/-- The kind of the certificate is one of the three alternatives.  This is the checked
`cases`-free form of the classification: every certificate reduces to neck, cap or compact
spherical. -/
theorem kind_cases (C : CanonicalNeighborhoodCertificate ε κ r X) :
    C.kind = CanonicalKind.neck ∨ C.kind = CanonicalKind.cap ∨
      C.kind = CanonicalKind.compactSpherical := by
  cases C.kind with
  | neck => exact Or.inl rfl
  | cap => exact Or.inr (Or.inl rfl)
  | compactSpherical => exact Or.inr (Or.inr rfl)

/-- **The neck alternative.**  A certificate whose kind is `neck` contains an ε-neck datum. -/
def neckOf (C : CanonicalNeighborhoodCertificate ε κ r X)
    (h : C.kind = CanonicalKind.neck) : EpsilonNeck ε r X :=
  C.neck_data h

/-- **The cap alternative.**  A certificate whose kind is `cap` contains an ε-cap datum. -/
def capOf (C : CanonicalNeighborhoodCertificate ε κ r X)
    (h : C.kind = CanonicalKind.cap) : EpsilonCap ε r X :=
  C.cap_data h

/-- **The compact-spherical alternative.**  A certificate whose kind is `compactSpherical`
contains an ε-spherical datum. -/
def sphericalOf (C : CanonicalNeighborhoodCertificate ε κ r X)
    (h : C.kind = CanonicalKind.compactSpherical) : EpsilonSpherical ε r X :=
  C.spherical_data h

/-- The scale is positive. -/
theorem scale_pos' (C : CanonicalNeighborhoodCertificate ε κ r X) : 0 < r :=
  C.scale_pos

end CanonicalNeighborhoodCertificate

end

end Canonical
end D7
end Poincare
