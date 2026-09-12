/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Mathlib.Analysis.InnerProductSpace.Orientation

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Volume.Basic

**D7 orientability and volume-form algebra layer, part 1: the oriented volume form on a
finite-dimensional real inner product space, its determinant interface, and orientation
reversal.**

This module is part of the `D7-orientability-volume-form` task. It consumes the accepted D6
weekly release unchanged and adds only files under `Poincare/D7/Volume/`.

## What mathlib (pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`) provides

The probe `Poincare/D7/Volume/Probe.lean` records the following checked facts, all reused here
and never redefined:

* `Orientation R M ι` — an orientation as a ray in the top alternating forms
  (`Mathlib/LinearAlgebra/Orientation.lean`);
* `Orientation.volumeForm : E [⋀^Fin n]→ₗ[ℝ] ℝ` — the nonvanishing top-dimensional alternating
  form of an oriented real inner product space
  (`Mathlib/Analysis/InnerProductSpace/Orientation.lean`);
* `Orientation.volumeForm_robust` / `Orientation.volumeForm_robust_neg` — the volume form is the
  determinant with respect to any positively (resp. negatively) oriented orthonormal basis;
* `Orientation.volumeForm_neg_orientation : (-o).volumeForm = -o.volumeForm` — the
  orientation-reversal sign law;
* `Orientation.volumeForm_comp_linearIsometryEquiv` — invariance under positively oriented
  isometries.

## What this file provides

* `VolumeFormData V` — the datum of an orientation of a finite-dimensional real inner product
  space, indexed by `Fin n` with `n = finrank ℝ V`. The dimension equality is a field, so the
  `Fact (finrank ℝ V = n)` instance needed by `Orientation.volumeForm` is available
  definitionally.
* `VolumeFormData.volumeForm` — the Riemannian volume form, definitionally the mathlib
  `Orientation.volumeForm`.
* `VolumeFormData.volumeForm_eq_det` — the **explicit determinant interface**: for every
  positively oriented orthonormal basis `b`, `D.volumeForm = b.toBasis.det`. The sign-reversed
  variant `volumeForm_eq_neg_det_of_orientation_ne` records that a negatively oriented
  orthonormal basis computes the negative determinant.
* `VolumeFormData.reverse` / `reverse_volumeForm` — the **orientation-reversal sign law**:
  reversing the orientation negates the volume form.
* `volumeForm_apply_basis`, `abs_volumeForm_apply_of_orthonormal` — normalisation on orthonormal
  bases, and the isometry (in)variance statements `volumeForm_comp_linearIsometryEquiv_of_det_pos`
  and `volumeForm_comp_linearIsometryEquiv_of_det_neg`.
* `VolumeFormData.std` — an inhabitant, so the definition is not vacuous.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

noncomputable section

open Module

namespace Poincare.D7.Volume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **An orientation of a finite-dimensional real inner product space**, in a form suitable for
the volume-form algebra: the dimension `n`, a proof `finrank ℝ V = n`, and an orientation
`Orientation ℝ V (Fin n)` of the top alternating forms.

The dimension equality is stored as a field (rather than requiring a global
`Fact (finrank ℝ V = n)` instance) so that every lemma below can install it locally with
`letI`; this keeps the data self-contained and avoids instance diamonds. -/
structure VolumeFormData (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] where
  /-- The dimension index of the orientation. -/
  n : ℕ
  /-- The dimension of `V` is `n`. -/
  finrank_eq : finrank ℝ V = n
  /-- The chosen orientation of `V`. -/
  orientation : Orientation ℝ V (Fin n)

namespace VolumeFormData

variable (D : VolumeFormData V)

/-- **The Riemannian volume form** of the oriented inner product space: the top-dimensional
alternating form associated with the orientation and the inner product. It is definitionally the
mathlib `Orientation.volumeForm`, so all of mathlib's volume-form API applies to it. -/
noncomputable def volumeForm : V [⋀^Fin D.n]→ₗ[ℝ] ℝ :=
  letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
  @Orientation.volumeForm V _ _ D.n _ D.orientation

@[simp]
theorem volumeForm_def : D.volumeForm =
    letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
    @Orientation.volumeForm V _ _ D.n _ D.orientation := rfl

/-- **The explicit determinant interface.** The volume form of an oriented inner product space is
the determinant with respect to any positively oriented orthonormal basis. This is mathlib's
`Orientation.volumeForm_robust`, packaged for `VolumeFormData`. -/
theorem volumeForm_eq_det (b : OrthonormalBasis (Fin D.n) ℝ V)
    (hb : b.toBasis.orientation = D.orientation) : D.volumeForm = b.toBasis.det := by
  letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
  exact Orientation.volumeForm_robust D.orientation b hb

/-- **The explicit determinant interface, negative orientation.** A negatively oriented
orthonormal basis computes the negative of the volume form. -/
theorem volumeForm_eq_neg_det_of_orientation_ne (b : OrthonormalBasis (Fin D.n) ℝ V)
    (hb : b.toBasis.orientation ≠ D.orientation) : D.volumeForm = -b.toBasis.det := by
  letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
  exact Orientation.volumeForm_robust_neg D.orientation b hb

/-- The volume form evaluated on a positively oriented orthonormal basis is `1`. -/
@[simp]
theorem volumeForm_apply_basis (b : OrthonormalBasis (Fin D.n) ℝ V)
    (hb : b.toBasis.orientation = D.orientation) : D.volumeForm b = 1 := by
  rw [D.volumeForm_eq_det b hb]
  simpa using (Basis.det_self b.toBasis)

/-- The absolute value of the volume form on any orthonormal basis is `1`. -/
theorem abs_volumeForm_apply_of_orthonormal (b : OrthonormalBasis (Fin D.n) ℝ V) :
    |D.volumeForm b| = 1 := by
  letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
  exact Orientation.abs_volumeForm_apply_of_orthonormal D.orientation b

/-- **Orientation reversal.** The datum with the opposite orientation. -/
def reverse (D : VolumeFormData V) : VolumeFormData V where
  n := D.n
  finrank_eq := D.finrank_eq
  orientation := -D.orientation

@[simp]
theorem reverse_n (D : VolumeFormData V) : D.reverse.n = D.n := rfl

@[simp]
theorem reverse_orientation (D : VolumeFormData V) :
    D.reverse.orientation = -D.orientation := rfl

/-- **The orientation-reversal sign law.** Reversing the orientation of the space negates the
volume form. This is mathlib's `Orientation.volumeForm_neg_orientation`, packaged for
`VolumeFormData`. -/
@[simp]
theorem reverse_volumeForm : D.reverse.volumeForm = -D.volumeForm := by
  letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
  exact Orientation.volumeForm_neg_orientation D.orientation

/-- The volume form is invariant under a positively oriented isometric automorphism. This is
mathlib's `Orientation.volumeForm_comp_linearIsometryEquiv`, packaged for `VolumeFormData`. -/
theorem volumeForm_comp_linearIsometryEquiv_of_det_pos (φ : V ≃ₗᵢ[ℝ] V)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : V →ₗ[ℝ] V)) (v : Fin D.n → V) :
    D.volumeForm (φ ∘ v) = D.volumeForm v := by
  letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
  exact Orientation.volumeForm_comp_linearIsometryEquiv D.orientation φ hφ v

/-- **The orientation-reversing isometry sign law.** An isometric automorphism with negative
determinant (an orientation-reversing isometry) changes the sign of the volume form. -/
theorem volumeForm_comp_linearIsometryEquiv_of_det_neg (φ : V ≃ₗᵢ[ℝ] V)
    (hφ : LinearMap.det (φ.toLinearEquiv : V →ₗ[ℝ] V) < 0) (v : Fin D.n → V) :
    D.volumeForm (φ ∘ v) = -D.volumeForm v := by
  letI : Fact (finrank ℝ V = D.n) := ⟨D.finrank_eq⟩
  have hcard : Fintype.card (Fin D.n) = finrank ℝ V := by simp [D.finrank_eq]
  have hmap : Orientation.map (Fin D.n) φ.toLinearEquiv D.orientation = -D.orientation :=
    (Orientation.map_eq_neg_iff_det_neg D.orientation φ.toLinearEquiv hcard).2 hφ
  have h1 : (-D.orientation).volumeForm (φ ∘ v) = D.volumeForm v := by
    rw [← hmap, Orientation.volumeForm_map]
    congr 1
    funext i
    simp
  have h2 : (-D.orientation).volumeForm (φ ∘ v) = -D.volumeForm (φ ∘ v) := by
    simp [Orientation.volumeForm_neg_orientation]
  linarith

/-- **The standard volume-form datum** of a finite-dimensional real inner product space: the
orientation of `stdOrthonormalBasis`. This witnesses that `VolumeFormData` is inhabited. -/
noncomputable def std (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : VolumeFormData V where
  n := finrank ℝ V
  finrank_eq := rfl
  orientation := (stdOrthonormalBasis ℝ V).toBasis.orientation

@[simp]
theorem std_n : (std V).n = finrank ℝ V := rfl

/-- The standard datum's volume form is the determinant of the standard orthonormal basis. -/
theorem std_volumeForm_eq_det :
    (std V).volumeForm = (stdOrthonormalBasis ℝ V).toBasis.det :=
  (std V).volumeForm_eq_det (stdOrthonormalBasis ℝ V) rfl

end VolumeFormData

end Poincare.D7.Volume
