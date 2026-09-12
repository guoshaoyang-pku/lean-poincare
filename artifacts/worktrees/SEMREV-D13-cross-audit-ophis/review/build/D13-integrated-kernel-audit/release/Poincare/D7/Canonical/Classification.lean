/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface, part 4: the classification toy — the certificate
excludes the collapsed model at a positive scale.**

The canonical neighborhood classification is a *non-collapsing* statement: a region that
carries a certificate at scale `r > 0` cannot be a single point, because each of the three
model interfaces contains a pair of points at distance at least `r` (`π r` for the cylinder
cross-section and the sphere, `r` for the cap boundary), and a single point can only be
ε-close to a model whose diameter is at most `2 ε`.

This module proves that quantitatively:

* `epsilonApproximation_dist_le_two_mul`: any ε-approximation out of a subsingleton region
  maps any two points of the target to within `2 ε`;
* `scale_le_two_mul_of_subsingleton`: every certificate on a subsingleton region satisfies
  `r ≤ 2 ε`;
* `degenerateModel_not_certificate`: the collapsed (one-point) model carries no certificate at
  scale `r` whenever `2 ε < r`;
* the three `isEmpty_*` lemmas isolate the same exclusion on each individual alternative;
* `exists_far_pair_of_certificate`: on an arbitrary region, a certificate yields a pair of
  points at distance at least `r - 3 ε`.

The toy is deliberately independent of any manifold structure: it is a statement about the
model interfaces and the ε-approximation datum over the D7 compactness layer.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

import Poincare.D7.Canonical.Models
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace Poincare
namespace D7
namespace Canonical

universe u

open Poincare.D7.Compactness

noncomputable section

/-! ## 1. The collapsed model -/

/-- **The degenerate model: the one-point (collapsed) pointed space.**  This is the
zero-scale limit of the cylinder cross-section; the classification toy shows that the
certificate at a positive scale excludes it. -/
abbrev degenerateModel : PointedMetricSpace.{0} := PointedMetricSpace.unit

/-- The collapsed model is the one-point space. -/
theorem degenerateModel_base : degenerateModel.base = PUnit.unit := rfl

/-! ## 2. The two-point bound for approximations out of a subsingleton -/

/-- **A single point can only be ε-close to a model of diameter at most `2 ε`.**  If `X` is a
subsingleton (the collapsed model), then any ε-approximation `X → Y` forces every pair of
points of `Y` to be within `2 ε`: surjectivity produces preimages, and a subsingleton has at
most one. -/
theorem epsilonApproximation_dist_le_two_mul {ε : ℝ} {X : PointedMetricSpace.{u}}
    [Subsingleton X] {Y : PointedMetricSpace.{u}} (A : EpsilonApproximation ε X Y)
    (y₁ y₂ : Y) : dist y₁ y₂ ≤ 2 * ε := by
  obtain ⟨x₁, hx₁⟩ := A.surjective y₁
  obtain ⟨x₂, hx₂⟩ := A.surjective y₂
  have hsub : x₁ = x₂ := Subsingleton.elim x₁ x₂
  have h3 : dist (A.approx x₁) (A.approx x₂) = 0 := by
    rw [hsub, dist_self]
  have h4 : dist (A.approx x₂) y₂ ≤ ε := by
    rw [dist_comm]
    exact hx₂
  calc dist y₁ y₂
      ≤ dist y₁ (A.approx x₁) + dist (A.approx x₁) (A.approx x₂)
          + dist (A.approx x₂) y₂ := dist_triangle4 _ _ _ _
    _ ≤ ε + 0 + ε := by linarith
    _ = 2 * ε := by ring

/-- The collapsed model is 0-close to itself: the exclusion below is about the positive model
scale, not about the ε-approximation notion. -/
theorem degenerateModel_approximates_itself {ε : ℝ} (hε : 0 ≤ ε) :
    Nonempty (EpsilonApproximation ε degenerateModel degenerateModel) :=
  ⟨EpsilonApproximation.refl degenerateModel hε⟩

/-! ## 3. The exclusion on each alternative -/

/-- **The collapsed model is not an ε-neck at scale `r` when `2 ε < r`.**  The cylinder
interface's cross-section antipodes are at distance `π r ≥ r`. -/
theorem isEmpty_epsilonNeck_degenerateModel {ε r : ℝ} (h : 2 * ε < r) :
    IsEmpty (EpsilonNeck ε r degenerateModel) := by
  constructor
  intro N
  have hd : dist N.model.space.base N.model.antipodal ≤ 2 * ε :=
    epsilonApproximation_dist_le_two_mul N.approx _ _
  rw [N.antipodal_dist] at hd
  have hr : 0 < r := N.radius_pos
  have hpi : r ≤ Real.pi * r := by nlinarith [Real.pi_gt_three]
  linarith

/-- **The collapsed model is not an ε-cap at scale `r` when `2 ε < r`.**  The cap boundary is
at distance `r`. -/
theorem isEmpty_epsilonCap_degenerateModel {ε r : ℝ} (h : 2 * ε < r) :
    IsEmpty (EpsilonCap ε r degenerateModel) := by
  constructor
  intro C
  have hd : dist C.model.space.base C.model.boundary ≤ 2 * ε :=
    epsilonApproximation_dist_le_two_mul C.approx _ _
  rw [C.boundary_dist] at hd
  linarith

/-- **The collapsed model is not an ε-spherical region at scale `r` when `2 ε < r`.**  The
sphere antipodes are at distance `π r ≥ r`. -/
theorem isEmpty_epsilonSpherical_degenerateModel {ε r : ℝ} (h : 2 * ε < r) :
    IsEmpty (EpsilonSpherical ε r degenerateModel) := by
  constructor
  intro S
  have hd : dist S.model.space.base S.model.antipodal ≤ 2 * ε :=
    epsilonApproximation_dist_le_two_mul S.approx _ _
  rw [S.antipodal_dist] at hd
  have hr : 0 < r := S.radius_pos
  have hpi : r ≤ Real.pi * r := by nlinarith [Real.pi_gt_three]
  linarith

/-! ## 4. The certificate-level exclusion -/

/-- **Every certificate on a subsingleton region has scale at most `2 ε`.**  This is the
quantitative classification content of the toy: the three alternatives all force a pair of
points at distance at least `r`, and a collapsed region cannot be `ε`-close to such a model. -/
theorem scale_le_two_mul_of_subsingleton {ε κ r : ℝ} {X : PointedMetricSpace.{u}}
    [Subsingleton X] (C : CanonicalNeighborhoodCertificate ε κ r X) : r ≤ 2 * ε := by
  rcases C.kind_cases with hk | hk | hk
  · have N := C.neck_data hk
    have hd : dist N.model.space.base N.model.antipodal ≤ 2 * ε :=
      epsilonApproximation_dist_le_two_mul N.approx _ _
    rw [N.antipodal_dist] at hd
    have hr : 0 < r := N.radius_pos
    have hpi : r ≤ Real.pi * r := by nlinarith [Real.pi_gt_three]
    linarith
  · have Cp := C.cap_data hk
    have hd : dist Cp.model.space.base Cp.model.boundary ≤ 2 * ε :=
      epsilonApproximation_dist_le_two_mul Cp.approx _ _
    rw [Cp.boundary_dist] at hd
    linarith
  · have S := C.spherical_data hk
    have hd : dist S.model.space.base S.model.antipodal ≤ 2 * ε :=
      epsilonApproximation_dist_le_two_mul S.approx _ _
    rw [S.antipodal_dist] at hd
    have hr : 0 < r := S.radius_pos
    have hpi : r ≤ Real.pi * r := by nlinarith [Real.pi_gt_three]
    linarith

/-- **The collapsed model carries no canonical-neighborhood certificate at scale `r` when
`2 ε < r`.**  This is the stated classification toy: the certificate's positive scale and the
model geometry exclude the degenerate (one-point) model. -/
theorem degenerateModel_not_certificate {ε κ r : ℝ} (h : 2 * ε < r) :
    ¬ Nonempty (CanonicalNeighborhoodCertificate ε κ r degenerateModel) := by
  rintro ⟨C⟩
  have hle : r ≤ 2 * ε := scale_le_two_mul_of_subsingleton C
  linarith

/-- **Contrapositive form.**  A certificate on the collapsed model forces `2 ε ≥ r`; the
positive-scale statement `2 ε < r` is therefore incompatible with collapse. -/
theorem not_two_mul_lt_of_degenerateModel_certificate {ε κ r : ℝ}
    (C : CanonicalNeighborhoodCertificate ε κ r degenerateModel) : ¬ 2 * ε < r := by
  intro h
  exact degenerateModel_not_certificate h ⟨C⟩

/-! ## 5. The general metric-size consequence -/

/-- **An ε-approximation transfers lower diameter bounds with error `3 ε`.**  If two points of
the target are at distance at least `c`, then the source has two points at distance at least
`c - 3 ε`: the approximation is `ε`-surjective twice and has distortion `ε`. -/
theorem exists_pair_of_le_dist_of_epsilonApproximation {ε c : ℝ} {X Y : PointedMetricSpace.{u}}
    (A : EpsilonApproximation ε X Y) {y₁ y₂ : Y} (h : c ≤ dist y₁ y₂) :
    ∃ x₁ x₂ : X, c ≤ dist x₁ x₂ + 3 * ε := by
  obtain ⟨x₁, hx₁⟩ := A.surjective y₁
  obtain ⟨x₂, hx₂⟩ := A.surjective y₂
  refine ⟨x₁, x₂, ?_⟩
  have h2 : dist (A.approx x₁) (A.approx x₂) ≤ dist x₁ x₂ + ε := A.dist_approx_le x₁ x₂
  have h3 : dist (A.approx x₂) y₂ ≤ ε := by
    rw [dist_comm]
    exact hx₂
  calc c ≤ dist y₁ y₂ := h
    _ ≤ dist y₁ (A.approx x₁) + dist (A.approx x₁) (A.approx x₂)
          + dist (A.approx x₂) y₂ := dist_triangle4 _ _ _ _
    _ ≤ ε + (dist x₁ x₂ + ε) + ε := by linarith
    _ = dist x₁ x₂ + 3 * ε := by ring

/-- **The certificate forces a positive metric size at its scale.**  Every certificate on an
arbitrary region `X` yields two points of `X` at distance at least `r - 3 ε`; for `3 ε < r`
this is a strictly positive lower bound. -/
theorem exists_far_pair_of_certificate {ε κ r : ℝ} {X : PointedMetricSpace.{u}}
    (C : CanonicalNeighborhoodCertificate ε κ r X) :
    ∃ x y : X, r ≤ dist x y + 3 * ε := by
  rcases C.kind_cases with hk | hk | hk
  · have N := C.neck_data hk
    have hle : r ≤ dist N.model.space.base N.model.antipodal := by
      rw [N.antipodal_dist]
      have hr : 0 < r := N.radius_pos
      nlinarith [Real.pi_gt_three]
    obtain ⟨x₁, x₂, hx⟩ :=
      exists_pair_of_le_dist_of_epsilonApproximation N.approx hle
    exact ⟨x₁, x₂, hx⟩
  · have Cp := C.cap_data hk
    have hle : r ≤ dist Cp.model.space.base Cp.model.boundary := by
      rw [Cp.boundary_dist]
    obtain ⟨x₁, x₂, hx⟩ :=
      exists_pair_of_le_dist_of_epsilonApproximation Cp.approx hle
    exact ⟨x₁, x₂, hx⟩
  · have S := C.spherical_data hk
    have hle : r ≤ dist S.model.space.base S.model.antipodal := by
      rw [S.antipodal_dist]
      have hr : 0 < r := S.radius_pos
      nlinarith [Real.pi_gt_three]
    obtain ⟨x₁, x₂, hx⟩ :=
      exists_pair_of_le_dist_of_epsilonApproximation S.approx hle
    exact ⟨x₁, x₂, hx⟩

end

end Canonical
end D7
end Poincare
