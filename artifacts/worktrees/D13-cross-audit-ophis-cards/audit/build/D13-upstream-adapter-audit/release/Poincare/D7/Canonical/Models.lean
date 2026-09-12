/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface, part 3: the model instance checks.**

This module checks that the three model interfaces of `Poincare.D7.Canonical.Basic` inhabit
the canonical-neighborhood data:

* `cylinder_certificate`: a cylinder interface of radius `r` is an ε-neck certificate at scale
  `r` (kind `neck`), for every `ε ≥ 0` and every `κ ≤ π`;
* `cap_certificate`: a cap interface of radius `r` is an ε-cap certificate at scale `r` (kind
  `cap`), for every `ε ≥ 0` and every `κ ≤ 1`;
* `sphere_certificate`: a sphere interface of radius `r` is a compact-spherical certificate at
  scale `r` (kind `compactSpherical`), for every `ε ≥ 0` and every `κ ≤ π`.

The approximation in every case is the identity (the model is 0-close to itself), so the
checks are kernel-checked for every `ε ≥ 0`, not merely for a positive ε.

The file also exhibits concrete pointed metric spaces inhabiting the three interfaces at the
scale `r = 2` (a line with two points at distance `2π`, an interval of diameter `2π` and an
interval of diameter `4`), so that the interface field systems are demonstrably consistent and
the certificates are non-vacuous at a scale where the D7 `so(3)` curvature normalization
`so3CurvatureScaleDatum` applies.

**Honest boundary.** The concrete witnesses are metric spaces whose *interfaces* are checked;
they are not the smooth round cylinder `S²(2) × ℝ` or the smooth round sphere `S³(2)`.  The
smooth round models are a named missing input in `Poincare.D7.Canonical.Statements`.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

import Poincare.D7.Canonical.Curvature
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace Poincare
namespace D7
namespace Canonical

universe u

open Poincare.D7.Compactness

noncomputable section

/-! ## 1. The cylinder interface is an ε-neck certificate -/

/-- **Instance check: a round-cylinder interface is an ε-neck at its own scale.**  The
region is the model itself, approximated by the identity, so the error is `0 ≤ ε`. -/
def cylinder_isEpsilonNeck (C : CylinderInterface.{u}) {ε : ℝ} (hε : 0 ≤ ε) :
    EpsilonNeck ε C.radius C.space where
  model := C
  radius_eq := rfl
  approx := EpsilonApproximation.refl C.space hε

/-- **Instance check: a round-cylinder interface is a canonical-neighborhood certificate of
kind `neck`** at its own scale, with any metric-noncollapsing constant `κ ≤ π` (the cylinder
cross-section has diameter `π r`). -/
def cylinder_certificate (C : CylinderInterface.{u}) {ε κ : ℝ} (hε : 0 ≤ ε)
    (hκ0 : 0 < κ) (hκ : κ ≤ Real.pi)
    (curvature : CurvatureScaleDatum.{u, u} C.radius) :
    CanonicalNeighborhoodCertificate ε κ C.radius C.space where
  scale_pos := C.radius_pos
  kind := CanonicalKind.neck
  neck_data := fun _ => cylinder_isEpsilonNeck C hε
  cap_data := fun h => by cases h
  spherical_data := fun h => by cases h
  curvature := curvature
  noncollapsing :=
    { κ_pos := hκ0
      farPoint := C.antipodal
      far_dist := by
        rw [C.antipodal_dist]
        exact mul_le_mul_of_nonneg_right hκ (le_of_lt C.radius_pos) }

/-! ## 2. The cap interface is an ε-cap certificate -/

/-- **Instance check: a round-cap interface is an ε-cap at its own scale.** -/
def cap_isEpsilonCap (C : CapInterface.{u}) {ε : ℝ} (hε : 0 ≤ ε) :
    EpsilonCap ε C.radius C.space where
  model := C
  radius_eq := rfl
  approx := EpsilonApproximation.refl C.space hε

/-- **Instance check: a round-cap interface is a canonical-neighborhood certificate of kind
`cap`** at its own scale, with any metric-noncollapsing constant `κ ≤ 1` (the cap boundary is
at distance `r`). -/
def cap_certificate (C : CapInterface.{u}) {ε κ : ℝ} (hε : 0 ≤ ε)
    (hκ0 : 0 < κ) (hκ : κ ≤ 1)
    (curvature : CurvatureScaleDatum.{u, u} C.radius) :
    CanonicalNeighborhoodCertificate ε κ C.radius C.space where
  scale_pos := C.radius_pos
  kind := CanonicalKind.cap
  neck_data := fun h => by cases h
  cap_data := fun _ => cap_isEpsilonCap C hε
  spherical_data := fun h => by cases h
  curvature := curvature
  noncollapsing :=
    { κ_pos := hκ0
      farPoint := C.boundary
      far_dist := by
        rw [C.boundary_dist]
        calc κ * C.radius ≤ 1 * C.radius :=
              mul_le_mul_of_nonneg_right hκ (le_of_lt C.radius_pos)
          _ = C.radius := one_mul _ }

/-! ## 3. The sphere interface is a compact-spherical certificate -/

/-- **Instance check: a round-sphere interface is an ε-spherical region at its own scale.** -/
def sphere_isEpsilonSpherical (S : SphereInterface.{u}) {ε : ℝ} (hε : 0 ≤ ε) :
    EpsilonSpherical ε S.radius S.space where
  model := S
  radius_eq := rfl
  approx := EpsilonApproximation.refl S.space hε

/-- **Instance check: a round-sphere interface is a canonical-neighborhood certificate of
kind `compactSpherical`** at its own scale, with any metric-noncollapsing constant `κ ≤ π`
(the sphere diameter is `π r`). -/
def sphere_certificate (S : SphereInterface.{u}) {ε κ : ℝ} (hε : 0 ≤ ε)
    (hκ0 : 0 < κ) (hκ : κ ≤ Real.pi)
    (curvature : CurvatureScaleDatum.{u, u} S.radius) :
    CanonicalNeighborhoodCertificate ε κ S.radius S.space where
  scale_pos := S.radius_pos
  kind := CanonicalKind.compactSpherical
  neck_data := fun h => by cases h
  cap_data := fun h => by cases h
  spherical_data := fun _ => sphere_isEpsilonSpherical S hε
  curvature := curvature
  noncollapsing :=
    { κ_pos := hκ0
      farPoint := S.antipodal
      far_dist := by
        rw [S.antipodal_dist]
        exact mul_le_mul_of_nonneg_right hκ (le_of_lt S.radius_pos) }

/-! ## 4. Concrete metric-space witnesses of the three interfaces at scale `2` -/

/-- The pointed real line, the metric-space witness of the cylinder interface. -/
abbrev lineSpace : PointedMetricSpace.{0} where
  M := ℝ
  inst := inferInstance
  base := 0

/-- **A line interface witness at scale `2`.**  The axis is the identity, the two points
`0` and `2π` play the role of the cross-section antipodes at distance `π · 2`.  This checks
the field system of `CylinderInterface`; it is not the round cylinder. -/
def lineCylinderInterface : CylinderInterface.{0} where
  space := lineSpace
  radius := 2
  radius_pos := by norm_num
  axis := id
  axis_base := rfl
  axis_dist := by
    intro s t
    exact Real.dist_eq s t
  antipodal := 2 * Real.pi
  antipodal_dist := by
    rw [Real.dist_eq]
    rw [show (0 : ℝ) - 2 * Real.pi = -(2 * Real.pi) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
    ring
  scalarCurvature := 1 / 2
  scalarCurvature_eq := by norm_num

/-- The closed interval `[-π, π]` with basepoint `-π`, the metric-space witness of the sphere
interface at scale `2`. -/
abbrev piIntervalSpace : PointedMetricSpace.{0} where
  M := Set.Icc (-Real.pi) Real.pi
  inst := inferInstance
  base := ⟨-Real.pi, by constructor <;> linarith [Real.pi_pos]⟩

/-- **An interval interface witness at scale `2`.**  The interval `[-π, π]` has diameter `2π`
and endpoints at distance `π · 2`; this checks the field system of `SphereInterface`.  It is
not the round sphere. -/
def piIntervalSphereInterface : SphereInterface.{0} where
  space := piIntervalSpace
  radius := 2
  radius_pos := by norm_num
  antipodal := ⟨Real.pi, by constructor <;> linarith [Real.pi_pos]⟩
  antipodal_dist := by
    rw [Subtype.dist_eq, Real.dist_eq]
    rw [show (-Real.pi : ℝ) - Real.pi = -(2 * Real.pi) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
    ring
  diameter_le := by
    intro x y
    rw [Subtype.dist_eq, Real.dist_eq, abs_le]
    constructor <;> linarith [x.2.1, x.2.2, y.2.1, y.2.2]
  scalarCurvature := 3 / 2
  scalarCurvature_eq := by norm_num

/-- The closed interval `[-2, 2]` with basepoint `0`, the metric-space witness of the cap
interface at scale `2`. -/
abbrev twoIntervalSpace : PointedMetricSpace.{0} where
  M := Set.Icc (-2 : ℝ) 2
  inst := inferInstance
  base := ⟨0, by constructor <;> norm_num⟩

/-- **An interval interface witness at scale `2`.**  The interval `[-2, 2]` has the boundary
point `2` at distance `2 = r` from the basepoint and diameter `4 ≤ 2π`; this checks the field
system of `CapInterface`.  It is not the round cap. -/
def twoIntervalCapInterface : CapInterface.{0} where
  space := twoIntervalSpace
  radius := 2
  radius_pos := by norm_num
  boundary := ⟨2, by constructor <;> norm_num⟩
  boundary_dist := by
    rw [Subtype.dist_eq, Real.dist_eq]
    norm_num
  diameter_le := by
    intro x y
    rw [Subtype.dist_eq, Real.dist_eq, abs_le]
    constructor <;> linarith [x.2.1, x.2.2, y.2.1, y.2.2, Real.pi_gt_three]
  scalarCurvature := 3 / 2
  scalarCurvature_eq := by norm_num

/-! ## 5. Concrete certificates at scale `2` with the `so(3)` curvature normalization -/

/-- **The line cylinder is an ε-neck at scale `2`.** -/
def lineCylinder_isEpsilonNeck {ε : ℝ} (hε : 0 ≤ ε) :
    EpsilonNeck ε 2 lineCylinderInterface.space :=
  cylinder_isEpsilonNeck lineCylinderInterface hε

/-- **The line cylinder is a canonical-neighborhood certificate of kind `neck` at scale `2`**,
with the D7 `so(3)` curvature normalization. -/
def lineCylinder_certificate {ε κ : ℝ} (hε : 0 ≤ ε) (hκ0 : 0 < κ)
    (hκ : κ ≤ Real.pi) :
    CanonicalNeighborhoodCertificate ε κ 2 lineCylinderInterface.space :=
  cylinder_certificate lineCylinderInterface hε hκ0 hκ so3CurvatureScaleDatum

/-- **The interval sphere is a canonical-neighborhood certificate of kind `compactSpherical`
at scale `2`**, with the D7 `so(3)` curvature normalization. -/
def piIntervalSphere_certificate {ε κ : ℝ} (hε : 0 ≤ ε) (hκ0 : 0 < κ)
    (hκ : κ ≤ Real.pi) :
    CanonicalNeighborhoodCertificate ε κ 2 piIntervalSphereInterface.space :=
  sphere_certificate piIntervalSphereInterface hε hκ0 hκ so3CurvatureScaleDatum

/-- **The interval cap is a canonical-neighborhood certificate of kind `cap` at scale `2`**,
with the D7 `so(3)` curvature normalization. -/
def twoIntervalCap_certificate {ε κ : ℝ} (hε : 0 ≤ ε) (hκ0 : 0 < κ) (hκ : κ ≤ 1) :
    CanonicalNeighborhoodCertificate ε κ 2 twoIntervalCapInterface.space :=
  cap_certificate twoIntervalCapInterface hε hκ0 hκ so3CurvatureScaleDatum

/-- **A neck certificate is inhabited at scale `2`**, on the line cylinder. -/
theorem exists_neck_certificate :
    Nonempty (CanonicalNeighborhoodCertificate 0 1 2 lineCylinderInterface.space) :=
  ⟨lineCylinder_certificate le_rfl (by norm_num) (by linarith [Real.pi_gt_three])⟩

/-- **A cap certificate is inhabited at scale `2`**, on the interval cap. -/
theorem exists_cap_certificate :
    Nonempty (CanonicalNeighborhoodCertificate 0 1 2 twoIntervalCapInterface.space) :=
  ⟨twoIntervalCap_certificate le_rfl (by norm_num) (by norm_num)⟩

/-- **A compact-spherical certificate is inhabited at scale `2`**, on the interval sphere. -/
theorem exists_spherical_certificate :
    Nonempty (CanonicalNeighborhoodCertificate 0 1 2 piIntervalSphereInterface.space) :=
  ⟨piIntervalSphere_certificate le_rfl (by norm_num) (by linarith [Real.pi_gt_three])⟩

/-- **All three kinds of certificate are inhabited at scale `2`.**  This is the non-vacuity
check of the canonical-neighborhood classification over the D7 curvature and compactness
layers: the neck, cap and compact-spherical alternatives each have a kernel-checked witness,
all sharing the D7 `so(3)` curvature normalization. -/
theorem exists_all_kinds_at_scale_two :
    (∃ X : PointedMetricSpace.{0}, Nonempty (CanonicalNeighborhoodCertificate 0 1 2 X)) ∧
    (∃ X : PointedMetricSpace.{0}, Nonempty (CanonicalNeighborhoodCertificate 0 1 2 X)) ∧
    (∃ X : PointedMetricSpace.{0}, Nonempty (CanonicalNeighborhoodCertificate 0 1 2 X)) :=
  ⟨⟨lineCylinderInterface.space, exists_neck_certificate⟩,
    ⟨twoIntervalCapInterface.space, exists_cap_certificate⟩,
    ⟨piIntervalSphereInterface.space, exists_spherical_certificate⟩⟩

end

end Canonical
end D7
end Poincare
