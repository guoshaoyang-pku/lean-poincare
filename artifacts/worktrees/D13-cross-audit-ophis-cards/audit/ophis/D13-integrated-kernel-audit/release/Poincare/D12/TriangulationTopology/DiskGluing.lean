/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gluing two disks along their boundary: the Alexander trick and sphere recognition

This file proves the *gluing lemma for sphere recognition* in its sharp form: if two
`(n+1)`-disks are glued along their boundary by an **arbitrary** homeomorphism
`h : 𝕊ⁿ ≃ₜ 𝕊ⁿ`, the resulting quotient is again the `(n+1)`-sphere:

  `diskGlueQuotHomeoSphere n h : DiskGlueQuot n h ≃ₜ Sphere (n+1)`.

The engine is the classical **Alexander trick**: every homeomorphism of `𝕊ⁿ` extends
radially to a homeomorphism of the closed disk `𝔻ⁿ⁺¹` (`alexanderHomeo`), with the
extension restricting to `h` on the boundary (`alexanderHomeo_sphereToDisk`).  The
arbitrary-boundary gluing therefore reduces, by quotient functoriality
(`quotMapHomeo`), to the identity gluing, which is the earlier theorem
`doubleDiskQuotHomeoSphere` of `SphereGluing.lean`.

The degeneracy checks are explicit: the extension is the identity exactly when `h` is
(`alexanderHomeo_eq_refl_iff`), it fixes the origin, and `diskGlueQuotHomeoSphere` at
`h = id` computes the previously proved gluing theorem
(`diskGlueQuotHomeoSphere_refl`).

## Contents

* `sphereBase`, `diskDirection`, `radialExtend` — the radial extension of a map of spheres;
* `continuous_radialExtend`, `radialExtend_zero`, `norm_radialExtend` — continuity and
  the norm identity `‖radialExtend φ x‖ = ‖x‖`;
* `alexanderHomeo`, `alexanderHomeo_sphereToDisk`, `alexanderHomeo_zero` — the Alexander
  trick homeomorphism of the disk and its boundary behaviour;
* `diskGlueRel`, `DiskGlueQuot`, `diskGlueQuotHomeoSphere` — the two-disk gluing theorem
  for an arbitrary boundary homeomorphism.

## Provenance

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned), Apache-2.0: imported
  lemmas only.  The Alexander trick and the gluing statement are classical; the proofs
  below are original for this worktree, no third-party proof is copied.
-/

import Poincare.D12.TriangulationTopology.SimplexCone

noncomputable section

open scoped Topology
open Filter Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## Part A: the Alexander trick (radial extension of sphere maps) -/

/-- The punctured closed disk, on which the direction map `x ↦ x/‖x‖` is continuous. -/
abbrev PuncturedDisk (n : ℕ) : Type :=
  {x : Disk (n + 1) // (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0}

/-- A base point of `𝕊ⁿ`, used only as the junk direction of the origin. -/
def sphereBase (n : ℕ) : Sphere n := Classical.choice (sphereNonempty n)

/-- **Unit direction** of a point of the closed disk: `x / ‖x‖` for `x ≠ 0`, with the
junk value `sphereBase n` at the origin (the value is irrelevant there because it is
multiplied by `‖x‖ = 0`). -/
def diskDirection (n : ℕ) (x : Disk (n + 1)) : Sphere n :=
  if hx : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 then sphereBase n
  else
    ⟨(‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ • (x : EuclideanSpace ℝ (Fin (n + 1))), by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

/-- On a nonzero point the direction is the normalization `x/‖x‖`. -/
theorem diskDirection_of_ne (n : ℕ) (x : Disk (n + 1))
    (hx : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) :
    diskDirection n x =
      ⟨(‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ •
        (x : EuclideanSpace ℝ (Fin (n + 1))), by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩ := by
  unfold diskDirection
  split_ifs with h
  · exact absurd h hx
  · rfl

/-- **Radial extension** of a map of spheres to a map of disks:
`x ↦ ‖x‖ • φ(x/‖x‖)`, with `0 ↦ 0`.  This is the map underlying the Alexander trick. -/
def radialExtend (n : ℕ) (φ : Sphere n → Sphere n) (x : Disk (n + 1)) : Disk (n + 1) :=
  ⟨‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ •
      (φ (diskDirection n x) : EuclideanSpace ℝ (Fin (n + 1))), by
    rw [mem_closedBall_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),
      mem_sphere_zero_iff_norm.mp (φ (diskDirection n x)).2, mul_one]
    simpa using mem_closedBall_iff_norm.mp x.2⟩

/-- Defining formula of the radial extension. -/
theorem radialExtend_apply (n : ℕ) (φ : Sphere n → Sphere n) (x : Disk (n + 1)) :
    (radialExtend n φ x : EuclideanSpace ℝ (Fin (n + 1))) =
      ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ •
        (φ (diskDirection n x) : EuclideanSpace ℝ (Fin (n + 1))) := rfl

/-- **Norm identity.** The radial extension preserves the distance to the origin:
`‖radialExtend φ x‖ = ‖x‖`.  In particular it maps the boundary sphere to itself. -/
theorem norm_radialExtend (n : ℕ) (φ : Sphere n → Sphere n) (x : Disk (n + 1)) :
    ‖(radialExtend n φ x : EuclideanSpace ℝ (Fin (n + 1)))‖ =
      ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
  rw [radialExtend_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    mem_sphere_zero_iff_norm.mp (φ (diskDirection n x)).2, mul_one]

/-- The origin is fixed by every radial extension. -/
@[simp] theorem radialExtend_zero (n : ℕ) (φ : Sphere n → Sphere n) :
    radialExtend n φ (0 : Disk (n + 1)) = 0 := by
  apply Subtype.ext
  rw [radialExtend_apply]
  simp

/-- The direction of the image point: radial extension commutes with taking the unit
direction. -/
theorem diskDirection_radialExtend (n : ℕ) (φ : Sphere n → Sphere n) (x : Disk (n + 1))
    (hx : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) :
    diskDirection n (radialExtend n φ x) = φ (diskDirection n x) := by
  have hnorm : (radialExtend n φ x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_radialExtend]
    exact norm_ne_zero_iff.mpr hx
  rw [diskDirection_of_ne n _ hnorm]
  apply Subtype.ext
  show ‖(radialExtend n φ x : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ •
      (radialExtend n φ x : EuclideanSpace ℝ (Fin (n + 1))) =
      (φ (diskDirection n x) : EuclideanSpace ℝ (Fin (n + 1)))
  rw [norm_radialExtend, radialExtend_apply, smul_smul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- The direction map is continuous on the punctured disk. -/
theorem continuous_diskDirection_punctured (n : ℕ) :
    Continuous fun x : PuncturedDisk n => diskDirection n x.1 := by
  have hcoe : Continuous fun x : PuncturedDisk n =>
      (x.1 : EuclideanSpace ℝ (Fin (n + 1))) := by fun_prop
  have hnorm : Continuous fun x : PuncturedDisk n =>
      ‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
    continuous_norm.comp hcoe
  have hinv : Continuous fun x : PuncturedDisk n =>
      (‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ :=
    hnorm.inv₀ fun x => norm_ne_zero_iff.mpr x.2
  have hf : Continuous fun x : PuncturedDisk n =>
      (‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ •
        (x.1 : EuclideanSpace ℝ (Fin (n + 1))) :=
    hinv.smul hcoe
  have hg : Continuous fun x : PuncturedDisk n =>
      (⟨(‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ •
        (x.1 : EuclideanSpace ℝ (Fin (n + 1))), by
          rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.2)]⟩ : Sphere n) :=
    Continuous.subtype_mk hf _
  exact hg.congr fun x => (diskDirection_of_ne n x.1 x.2).symm

/-- The direction map is continuous on the punctured disk (`ContinuousOn` form). -/
theorem continuousOn_diskDirection (n : ℕ) :
    ContinuousOn (diskDirection n) {x : Disk (n + 1) |
      (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_diskDirection_punctured n

/-- **Continuity of the radial extension.** -/
theorem continuous_radialExtend (n : ℕ) (φ : Sphere n → Sphere n) (hφ : Continuous φ) :
    Continuous (radialExtend n φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  by_cases hx : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0
  · -- at the origin: use `‖radialExtend φ y‖ = ‖y‖`
    rw [show x = 0 from Subtype.ext hx]
    have hnorm : Tendsto (fun y : Disk (n + 1) =>
        ‖(radialExtend n φ y : EuclideanSpace ℝ (Fin (n + 1)))‖) (𝓝 0) (𝓝 0) := by
      have hEq : (fun y : Disk (n + 1) =>
          ‖(radialExtend n φ y : EuclideanSpace ℝ (Fin (n + 1)))‖) =
          fun y : Disk (n + 1) => ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
        funext y
        exact norm_radialExtend n φ y
      rw [hEq]
      have hcont : Continuous fun y : Disk (n + 1) =>
          ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ := by fun_prop
      simpa using hcont.tendsto (0 : Disk (n + 1))
    change Tendsto (fun y : Disk (n + 1) => (radialExtend n φ y :
      EuclideanSpace ℝ (Fin (n + 1)))) (𝓝 0)
      (𝓝 ((radialExtend n φ (0 : Disk (n + 1)) : Disk (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 1))))
    simpa using tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  · -- away from the origin: rewrite as the manifestly continuous formula
    have hopen : IsOpen {y : Disk (n + 1) |
        (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0} :=
      isOpen_ne.preimage continuous_subtype_val
    have hcontOn : ContinuousOn (fun y : Disk (n + 1) =>
        ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ •
          (φ (diskDirection n y) : EuclideanSpace ℝ (Fin (n + 1))))
        {y : Disk (n + 1) | (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hcoe : Continuous fun y : PuncturedDisk n =>
          (y.1 : EuclideanSpace ℝ (Fin (n + 1))) := by fun_prop
      have hdir : Continuous fun y : PuncturedDisk n => diskDirection n y.1 :=
        continuous_diskDirection_punctured n
      have hphi : Continuous fun y : PuncturedDisk n =>
          (φ (diskDirection n y.1) : EuclideanSpace ℝ (Fin (n + 1))) :=
        continuous_subtype_val.comp (hφ.comp hdir)
      have hnorm : Continuous fun y : PuncturedDisk n =>
          ‖(y.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ := continuous_norm.comp hcoe
      exact hnorm.smul hphi
    refine (hcontOn.continuousAt (hopen.mem_nhds hx)).congr ?_
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact radialExtend_apply n φ y

/-- The boundary inclusion `𝕊ⁿ ↪ 𝔻ⁿ⁺¹` (the sphere as the boundary of the disk). -/
def sphereToDisk (n : ℕ) (x : Sphere n) : Disk (n + 1) :=
  ⟨(x : EuclideanSpace ℝ (Fin (n + 1))), by
    rw [mem_closedBall_iff_norm, sub_zero]
    exact le_of_eq (mem_sphere_zero_iff_norm.mp x.2)⟩

/-- The underlying vector of `sphereToDisk n x` is `x`. -/
@[simp] theorem sphereToDisk_coe (n : ℕ) (x : Sphere n) :
    ((sphereToDisk n x : Disk (n + 1)) : EuclideanSpace ℝ (Fin (n + 1))) =
      (x : EuclideanSpace ℝ (Fin (n + 1))) := rfl

/-- The direction of a boundary point is the point itself. -/
theorem diskDirection_sphereToDisk (n : ℕ) (x : Sphere n) :
    diskDirection n (sphereToDisk n x) = x := by
  have hne : (sphereToDisk n x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    intro h
    have hx0 : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := h
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 0 := by rw [hx0, norm_zero]
    rw [mem_sphere_zero_iff_norm.mp x.2] at hnorm
    exact one_ne_zero hnorm
  rw [diskDirection_of_ne n _ hne]
  apply Subtype.ext
  show (‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ •
    (x : EuclideanSpace ℝ (Fin (n + 1))) = (x : EuclideanSpace ℝ (Fin (n + 1)))
  rw [mem_sphere_zero_iff_norm.mp x.2, inv_one, one_smul]

/-- **Boundary behaviour of the radial extension.** On the boundary sphere, the radial
extension of `φ` is `φ` itself. -/
theorem radialExtend_sphereToDisk (n : ℕ) (φ : Sphere n → Sphere n) (x : Sphere n) :
    radialExtend n φ (sphereToDisk n x) = sphereToDisk n (φ x) := by
  apply Subtype.ext
  rw [radialExtend_apply, sphereToDisk_coe, diskDirection_sphereToDisk,
    mem_sphere_zero_iff_norm.mp x.2, one_smul, sphereToDisk_coe]

/-- Extending the identity map of the sphere gives the identity map of the disk. -/
theorem radialExtend_id (n : ℕ) :
    radialExtend n (id : Sphere n → Sphere n) = id := by
  funext y
  by_cases hy : (y : EuclideanSpace ℝ (Fin (n + 1))) = 0
  · rw [show y = 0 from Subtype.ext hy]
    simp
  · apply Subtype.ext
    rw [radialExtend_apply, diskDirection_of_ne n y hy]
    simp only [id_eq, Subtype.coe_mk]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

/-- Radial extension is compatible with composition: extending `φ ∘ ψ` is the composite
of the extensions. -/
theorem radialExtend_comp (n : ℕ) (φ ψ : Sphere n → Sphere n) (x : Disk (n + 1)) :
    radialExtend n φ (radialExtend n ψ x) = radialExtend n (φ ∘ ψ) x := by
  by_cases hx : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0
  · rw [show x = 0 from Subtype.ext hx]
    simp
  · apply Subtype.ext
    rw [radialExtend_apply, norm_radialExtend, diskDirection_radialExtend n ψ x hx,
      radialExtend_apply]
    rfl

/-- **The Alexander trick.** Every homeomorphism of `𝕊ⁿ` extends radially to a
homeomorphism of the closed disk `𝔻ⁿ⁺¹`, fixing the origin and restricting to `h` on the
boundary. -/
def alexanderHomeo (n : ℕ) (h : Sphere n ≃ₜ Sphere n) : Disk (n + 1) ≃ₜ Disk (n + 1) where
  toFun := radialExtend n h
  invFun := radialExtend n h.symm
  left_inv x := by
    have hcomp := radialExtend_comp n h.symm h x
    have hfun : (h.symm ∘ h : Sphere n → Sphere n) = id :=
      funext fun y => h.symm_apply_apply y
    rw [hfun, radialExtend_id] at hcomp
    exact hcomp
  right_inv x := by
    have hcomp := radialExtend_comp n h h.symm x
    have hfun : (h ∘ h.symm : Sphere n → Sphere n) = id :=
      funext fun y => h.apply_symm_apply y
    rw [hfun, radialExtend_id] at hcomp
    exact hcomp
  continuous_toFun := continuous_radialExtend n h h.continuous
  continuous_invFun := continuous_radialExtend n h.symm h.continuous_symm

/-- The Alexander extension is the identity for the identity boundary homeomorphism. -/
@[simp] theorem alexanderHomeo_refl (n : ℕ) :
    alexanderHomeo n (Homeomorph.refl (Sphere n)) = Homeomorph.refl (Disk (n + 1)) := by
  ext x : 1
  exact congrFun (radialExtend_id n) x

/-- The Alexander extension fixes the origin. -/
@[simp] theorem alexanderHomeo_zero (n : ℕ) (h : Sphere n ≃ₜ Sphere n) :
    alexanderHomeo n h (0 : Disk (n + 1)) = 0 :=
  radialExtend_zero n h

/-- **Boundary restriction.** On the boundary sphere, the Alexander extension of `h` is
exactly `h`. -/
theorem alexanderHomeo_sphereToDisk (n : ℕ) (h : Sphere n ≃ₜ Sphere n) (x : Sphere n) :
    alexanderHomeo n h (sphereToDisk n x) = sphereToDisk n (h x) :=
  radialExtend_sphereToDisk n h x

/-- **Nondegeneracy check.** A homeomorphism of the sphere is trivial iff its Alexander
extension is trivial. -/
theorem alexanderHomeo_eq_refl_iff (n : ℕ) (h : Sphere n ≃ₜ Sphere n) :
    alexanderHomeo n h = Homeomorph.refl (Disk (n + 1)) ↔ h = Homeomorph.refl (Sphere n) := by
  constructor
  · intro hh
    ext x : 1
    apply Subtype.ext
    have h1 := congrArg (fun (e : Disk (n + 1) ≃ₜ Disk (n + 1)) =>
      e (sphereToDisk n x)) hh
    rw [alexanderHomeo_sphereToDisk] at h1
    simpa using congrArg (fun y : Disk (n + 1) =>
      (y : EuclideanSpace ℝ (Fin (n + 1)))) h1
  · intro hh
    rw [hh]
    exact alexanderHomeo_refl n

/-! ## Part B: gluing two disks along an arbitrary boundary homeomorphism -/

/-- The gluing relation of two `(n+1)`-disks along their common boundary via
`h : 𝕊ⁿ ≃ₜ 𝕊ⁿ`: `inl x ~ inr (h x)` for `x` on the boundary sphere. -/
def diskGlueRel (n : ℕ) (h : Sphere n ≃ₜ Sphere n) : DoubleDisk n → DoubleDisk n → Prop :=
  fun p q => p = q ∨
    (∃ x : Sphere n,
      p = Sum.inl (sphereToDisk n x) ∧ q = Sum.inr (sphereToDisk n (h x))) ∨
    (∃ x : Sphere n,
      p = Sum.inr (sphereToDisk n (h x)) ∧ q = Sum.inl (sphereToDisk n x))

/-- The quotient of two `(n+1)`-disks glued along their boundary by `h`. -/
abbrev DiskGlueQuot (n : ℕ) (h : Sphere n ≃ₜ Sphere n) : Type := Quot (diskGlueRel n h)

/-- Computation rule for the quotient functoriality homeomorphism on classes. -/
@[simp] theorem quotMapHomeo_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {r : X → X → Prop} {s : Y → Y → Prop}
    (h : ∀ a b, r a b ↔ s (e a) (e b)) (a : X) :
    quotMapHomeo e h (Quot.mk r a) = Quot.mk s (e a) := rfl

/-- The disk homeomorphism acting on the disjoint union of the two disks: the first disk is
transported by the Alexander extension of `h`, the second is fixed.  It converts the
`h`-gluing into the identity gluing. -/
def diskGlueSumHomeo (n : ℕ) (h : Sphere n ≃ₜ Sphere n) : DoubleDisk n ≃ₜ DoubleDisk n :=
  Homeomorph.sumCongr (alexanderHomeo n h) (Homeomorph.refl (Disk (n + 1)))

@[simp] theorem diskGlueSumHomeo_inl (n : ℕ) (h : Sphere n ≃ₜ Sphere n) (d : Disk (n + 1)) :
    diskGlueSumHomeo n h (Sum.inl d) = Sum.inl (alexanderHomeo n h d) := rfl

@[simp] theorem diskGlueSumHomeo_inr (n : ℕ) (h : Sphere n ≃ₜ Sphere n) (d : Disk (n + 1)) :
    diskGlueSumHomeo n h (Sum.inr d) = Sum.inr d := rfl

/-- The inverse of the Alexander extension on a boundary point. -/
theorem alexanderHomeo_symm_sphereToDisk (n : ℕ) (h : Sphere n ≃ₜ Sphere n) (x : Sphere n) :
    (alexanderHomeo n h).symm (sphereToDisk n x) = sphereToDisk n (h.symm x) :=
  radialExtend_sphereToDisk n h.symm x

/-- **Relation transport.** The Alexander trick converts the gluing with boundary
homeomorphism `h` into the identity gluing: `diskGlueRel n h` is the pullback of
`diskGlueRel n id` along `diskGlueSumHomeo n h`. -/
theorem diskGlueRel_transport (n : ℕ) (h : Sphere n ≃ₜ Sphere n) (p q : DoubleDisk n) :
    diskGlueRel n h p q ↔
      diskGlueRel n (Homeomorph.refl (Sphere n))
        (diskGlueSumHomeo n h p) (diskGlueSumHomeo n h q) := by
  constructor
  · intro hpq
    rcases hpq with rfl | ⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact Or.inl rfl
    · refine Or.inr (Or.inl ⟨h x, ?_, ?_⟩)
      · rw [diskGlueSumHomeo_inl, alexanderHomeo_sphereToDisk]
      · rw [diskGlueSumHomeo_inr]
        simp
    · refine Or.inr (Or.inr ⟨h x, ?_, ?_⟩)
      · rw [diskGlueSumHomeo_inr]
        simp
      · rw [diskGlueSumHomeo_inl, alexanderHomeo_sphereToDisk]
  · intro hpq
    rcases p with d | d <;> rcases q with e | e
    · -- inl, inl
      rcases hpq with hpq | ⟨x, h1, h2⟩ | ⟨x, h1, h2⟩
      · exact Or.inl (Sum.inl_injective (β := Disk (n + 1))
          (by simpa [diskGlueSumHomeo_inl] using hpq))
      · exact absurd h2 (by simp [diskGlueSumHomeo_inl])
      · exact absurd h1 (by simp [diskGlueSumHomeo_inl])
    · -- inl, inr
      rcases hpq with hpq | ⟨x, h1, h2⟩ | ⟨x, h1, h2⟩
      · exact absurd hpq (by simp [diskGlueSumHomeo_inl, diskGlueSumHomeo_inr])
      · have h1' : (alexanderHomeo n h) d = sphereToDisk n x := by
          simpa [diskGlueSumHomeo_inl] using h1
        have h2' : e = sphereToDisk n x := by
          simpa [diskGlueSumHomeo_inr, Homeomorph.refl_apply] using h2
        refine Or.inr (Or.inl ⟨h.symm x, ?_, ?_⟩)
        · exact congrArg Sum.inl (by
            rw [← Homeomorph.symm_apply_apply (alexanderHomeo n h) d, h1',
              alexanderHomeo_symm_sphereToDisk])
        · rw [h2']
          simp
      · exact absurd h1 (by simp)
    · -- inr, inl
      rcases hpq with hpq | ⟨x, h1, h2⟩ | ⟨x, h1, h2⟩
      · exact absurd hpq (by simp)
      · exact absurd h2 (by simp)
      · have h1' : d = sphereToDisk n x := by
          simpa [diskGlueSumHomeo_inr, Homeomorph.refl_apply] using h1
        have h2' : (alexanderHomeo n h) e = sphereToDisk n x := by
          simpa [diskGlueSumHomeo_inl] using h2
        refine Or.inr (Or.inr ⟨h.symm x, ?_, ?_⟩)
        · rw [h1']
          simp
        · exact congrArg Sum.inl (by
            rw [← Homeomorph.symm_apply_apply (alexanderHomeo n h) e, h2',
              alexanderHomeo_symm_sphereToDisk])
    · -- inr, inr
      rcases hpq with hpq | ⟨x, h1, h2⟩ | ⟨x, h1, h2⟩
      · exact Or.inl (Sum.inr_injective (α := Disk (n + 1))
          (by simpa [diskGlueSumHomeo_inr] using hpq))
      · exact absurd h1 (by simp [diskGlueSumHomeo_inr])
      · exact absurd h2 (by simp [diskGlueSumHomeo_inr])

/-- **The identity gluing is the earlier double-disk relation.** -/
theorem diskGlueRel_id_iff_doubleDiskRel (n : ℕ) (p q : DoubleDisk n) :
    diskGlueRel n (Homeomorph.refl (Sphere n)) p q ↔ doubleDiskRel n p q := by
  constructor
  · intro hpq
    rcases hpq with rfl | ⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨sphereToDisk n x, sphereToDisk n x, rfl, rfl, rfl, x.2⟩)
    · exact Or.inr (Or.inr ⟨sphereToDisk n x, sphereToDisk n x, rfl, rfl, rfl, x.2⟩)
  · intro hpq
    rcases hpq with rfl | ⟨d, e, rfl, rfl, hde, hd⟩ | ⟨d, e, rfl, rfl, hde, hd⟩
    · exact Or.inl rfl
    · subst hde
      exact Or.inr (Or.inl ⟨⟨(d : EuclideanSpace ℝ (Fin (n + 1))), hd⟩, rfl, rfl⟩)
    · subst hde
      exact Or.inr (Or.inr ⟨⟨(d : EuclideanSpace ℝ (Fin (n + 1))), hd⟩, rfl, rfl⟩)

/-- **Gluing two disks along an arbitrary boundary homeomorphism gives the sphere.**
This is the sharp form of the sphere-recognition gluing lemma: the result does not depend
on the gluing homeomorphism `h : 𝕊ⁿ ≃ₜ 𝕊ⁿ`. -/
noncomputable def diskGlueQuotHomeoSphere (n : ℕ) (h : Sphere n ≃ₜ Sphere n) :
    DiskGlueQuot n h ≃ₜ Sphere (n + 1) :=
  (quotMapHomeo (diskGlueSumHomeo n h) (diskGlueRel_transport n h)).trans
    ((quotMapHomeo (Homeomorph.refl (DoubleDisk n))
      (diskGlueRel_id_iff_doubleDiskRel n)).trans (doubleDiskQuotHomeoSphere n))

/-- **Compactness audit.** The two-disk gluing quotient is compact (a quotient of the
compact disjoint union of two disks). -/
instance diskGlueQuotCompactSpace (n : ℕ) (h : Sphere n ≃ₜ Sphere n) :
    CompactSpace (DiskGlueQuot n h) :=
  Quot.compactSpace

/-- **T2 audit.** The two-disk gluing quotient is Hausdorff (transported along the
homeomorphism to the sphere). -/
instance diskGlueQuotT2Space (n : ℕ) (h : Sphere n ≃ₜ Sphere n) :
    T2Space (DiskGlueQuot n h) :=
  (diskGlueQuotHomeoSphere n h).symm.t2Space

/-- **Nonemptiness audit.** The two-disk gluing quotient is nonempty (class of the centre
of the first disk). -/
instance diskGlueQuotNonempty (n : ℕ) (h : Sphere n ≃ₜ Sphere n) :
    Nonempty (DiskGlueQuot n h) :=
  ⟨Quot.mk (diskGlueRel n h) (Sum.inl 0)⟩

/-- **Compatibility with the earlier theorem.** At the identity gluing, the new
homeomorphism is the previously proved `doubleDiskQuotHomeoSphere` after the canonical
identification `DiskGlueQuot n id ≅ DoubleDiskQuot n`; the value on a class is computed
explicitly. -/
theorem diskGlueQuotHomeoSphere_refl_apply (n : ℕ) (p : DoubleDisk n) :
    diskGlueQuotHomeoSphere n (Homeomorph.refl (Sphere n))
        (Quot.mk (diskGlueRel n (Homeomorph.refl (Sphere n))) p) =
      doubleDiskQuotHomeoSphere n (Quot.mk (doubleDiskRel n) p) := by
  have hA : diskGlueSumHomeo n (Homeomorph.refl (Sphere n)) =
      Homeomorph.refl (DoubleDisk n) := by
    rw [diskGlueSumHomeo, alexanderHomeo_refl, Homeomorph.sumCongr_refl]
  rw [diskGlueQuotHomeoSphere, Homeomorph.trans_apply, Homeomorph.trans_apply]
  rw [show (quotMapHomeo (diskGlueSumHomeo n (Homeomorph.refl (Sphere n)))
        (diskGlueRel_transport n (Homeomorph.refl (Sphere n))))
        (Quot.mk (diskGlueRel n (Homeomorph.refl (Sphere n))) p) =
      Quot.mk (diskGlueRel n (Homeomorph.refl (Sphere n)))
        (diskGlueSumHomeo n (Homeomorph.refl (Sphere n)) p) from rfl]
  rw [hA]
  rw [show (quotMapHomeo (Homeomorph.refl (DoubleDisk n))
        (diskGlueRel_id_iff_doubleDiskRel n))
        (Quot.mk (diskGlueRel n (Homeomorph.refl (Sphere n)))
          ((Homeomorph.refl (DoubleDisk n)) p)) =
      Quot.mk (doubleDiskRel n) p from rfl]

/-- **Shape check.** Two 3-balls glued along their boundary by any homeomorphism of `𝕊²`
form the 3-sphere. -/
example (h : Sphere 2 ≃ₜ Sphere 2) : DiskGlueQuot 2 h ≃ₜ Sphere 3 :=
  diskGlueQuotHomeoSphere 2 h

/-- **Shape check.** Two disks glued along their boundary form a circle. -/
example (h : Sphere 1 ≃ₜ Sphere 1) : DiskGlueQuot 1 h ≃ₜ Sphere 2 :=
  diskGlueQuotHomeoSphere 1 h

/-- **Shape check.** Two intervals glued along their (two-point) boundary form a circle:
the `n = 0` case. -/
example (h : Sphere 0 ≃ₜ Sphere 0) : DiskGlueQuot 0 h ≃ₜ Sphere 1 :=
  diskGlueQuotHomeoSphere 0 h

end Poincare.D12.TriangulationTopology
