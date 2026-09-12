/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Poincare.D7.Volume.Basic

set_option linter.style.haveILetI false

open scoped RealInnerProductSpace

/-!
# Poincare.D7.Volume.Scaling

**D7 orientability and volume-form algebra layer, part 2: the metric-scaling law
`vol (c • g) = c ^ (n / 2) • vol g`.**

This module proves the scaling law for the Riemannian volume form under a positive rescaling of
the metric, through the **explicit determinant interface** of `Poincare.D7.Volume.Basic`:
the volume form of a metric is the determinant with respect to a positively oriented orthonormal
basis, and rescaling the metric `g` by `c > 0` rescales the orthonormal basis by `(√c)⁻¹`, which
multiplies every determinant by `(√c) ^ n = c ^ (n / 2)`.

## Main definitions

* `sqrtInvUnit c hc` — the unit `(√c)⁻¹` of `ℝ` (the basis-rescaling factor).
* `VolumeFormData.scaledBasis b c hc` — the basis `b i ↦ (√c)⁻¹ • b i`, which is orthonormal for
  the rescaled metric `c • g` (`scaledBasis_orthonormal`) and has the same orientation as `b`
  (`scaledBasis_orientation`).
* `VolumeFormData.scaledVolumeForm b c hc` — the determinant in the scaled basis, i.e. the volume
  form of the metric `c • g` in the explicit determinant interface.

## Main results

* `VolumeFormData.scaledBasis_det_apply` — `det (scaledBasis) v = c ^ (n / 2) * det b v`.
* `VolumeFormData.volumeForm_smul_metric` — `vol (c • g) = c ^ (n / 2) • vol g` (as alternating
  maps), and the pointwise form `VolumeFormData.scaledVolumeForm_apply`.
* `sqrt_pow_eq_rpow_half` — `(√c) ^ n = c ^ (n / 2 : ℝ)` for `c > 0`, so the scaling factor is
  stated in the task's notation.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

noncomputable section

open Module

namespace Poincare.D7.Volume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The unit `(√c)⁻¹` of `ℝ`, used to rescale an orthonormal basis of `g` to an orthonormal basis
of `c • g`. -/
def sqrtInvUnit (c : ℝ) (hc : 0 < c) : ℝˣ :=
  Units.mk0 (Real.sqrt c)⁻¹ (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hc)))

@[simp]
theorem sqrtInvUnit_val (c : ℝ) (hc : 0 < c) :
    ((sqrtInvUnit c hc : ℝˣ) : ℝ) = (Real.sqrt c)⁻¹ := rfl

theorem sqrtInvUnit_pos (c : ℝ) (hc : 0 < c) : 0 < ((sqrtInvUnit c hc : ℝˣ) : ℝ) :=
  inv_pos.mpr (Real.sqrt_pos.2 hc)

/-- `(√c) ^ n = c ^ (n / 2 : ℝ)` for `c > 0`: the scaling factor of the volume form written in
the exponent notation of the task. -/
theorem sqrt_pow_eq_rpow_half (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Real.sqrt c ^ n = c ^ (n / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  congr 1
  ring

namespace VolumeFormData

variable (D : VolumeFormData V)

/-- **The orthonormal basis of the rescaled metric `c • g`.** If `b` is an orthonormal basis of
the metric `g`, then `i ↦ (√c)⁻¹ • b i` is an orthonormal basis of `c • g`; the volume form of
`c • g` is the determinant in this basis. -/
noncomputable def scaledBasis (b : OrthonormalBasis (Fin D.n) ℝ V) (c : ℝ) (hc : 0 < c) :
    Basis (Fin D.n) ℝ V :=
  b.toBasis.unitsSMul fun _ => sqrtInvUnit c hc

@[simp]
theorem scaledBasis_apply (b : OrthonormalBasis (Fin D.n) ℝ V) (c : ℝ) (hc : 0 < c)
    (i : Fin D.n) : D.scaledBasis b c hc i = (Real.sqrt c)⁻¹ • b i := by
  simp [scaledBasis, Basis.unitsSMul_apply, sqrtInvUnit]

/-- The scaled basis is orthonormal for the rescaled metric `c • g`, expressed with the explicit
bilinear form `(x, y) ↦ c * ⟪x, y⟫`. -/
theorem scaledBasis_orthonormal (b : OrthonormalBasis (Fin D.n) ℝ V) (c : ℝ) (hc : 0 < c)
    (i j : Fin D.n) :
    c * inner ℝ (D.scaledBasis b c hc i) (D.scaledBasis b c hc j) = if i = j then 1 else 0 := by
  rw [D.scaledBasis_apply, D.scaledBasis_apply]
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [orthonormal_iff_ite.mp b.orthonormal i j]
  have hsq : c = (Real.sqrt c) ^ 2 := (Real.sq_sqrt hc.le).symm
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  rw [hsq]
  field_simp
  rw [Real.sq_sqrt (sq_nonneg (Real.sqrt c))]

/-- Rescaling by a positive factor preserves the orientation given by the basis. -/
theorem scaledBasis_orientation (b : OrthonormalBasis (Fin D.n) ℝ V) (c : ℝ) (hc : 0 < c) :
    (D.scaledBasis b c hc).orientation = b.toBasis.orientation := by
  rw [scaledBasis, Basis.orientation_unitsSMul]
  rw [show (∏ _i : Fin D.n, sqrtInvUnit c hc) = (sqrtInvUnit c hc) ^ D.n by
    simp [Finset.prod_const, Fintype.card_fin]]
  apply Module.Ray.units_smul_of_pos
  have hpos : 0 < ((sqrtInvUnit c hc : ℝˣ) : ℝ) := sqrtInvUnit_pos c hc
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  exact inv_pos.mpr (pow_pos hpos D.n)

/-- **The determinant scaling law.** The determinant in the rescaled basis
`i ↦ (√c)⁻¹ • b i` is `(√c) ^ n = c ^ (n / 2)` times the determinant in `b`. -/
theorem scaledBasis_det_apply (b : OrthonormalBasis (Fin D.n) ℝ V) (c : ℝ) (hc : 0 < c)
    (v : Fin D.n → V) :
    (D.scaledBasis b c hc).det v = c ^ (D.n / 2 : ℝ) * b.toBasis.det v := by
  rw [scaledBasis, Basis.det_unitsSMul]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, AlternatingMap.smul_apply,
    smul_eq_mul]
  rw [show (↑((sqrtInvUnit c hc) ^ D.n)⁻¹ : ℝ) = Real.sqrt c ^ D.n by
    simp [sqrtInvUnit, Units.val_inv_eq_inv_val, inv_pow]]
  rw [sqrt_pow_eq_rpow_half c hc D.n]

/-- **The volume form of the rescaled metric `c • g`**, in the explicit determinant interface: the
determinant with respect to the `(c • g)`-orthonormal basis `D.scaledBasis b c hc`. -/
noncomputable def scaledVolumeForm (b : OrthonormalBasis (Fin D.n) ℝ V) (c : ℝ) (hc : 0 < c) :
    V [⋀^Fin D.n]→ₗ[ℝ] ℝ :=
  (D.scaledBasis b c hc).det

/-- Pointwise form of the scaling law: evaluating the volume form of `c • g` on a frame equals
`c ^ (n / 2)` times the volume form of `g`. -/
theorem scaledVolumeForm_apply (b : OrthonormalBasis (Fin D.n) ℝ V)
    (hb : b.toBasis.orientation = D.orientation) (c : ℝ) (hc : 0 < c) (v : Fin D.n → V) :
    D.scaledVolumeForm b c hc v = c ^ (D.n / 2 : ℝ) * D.volumeForm v := by
  rw [scaledVolumeForm, D.scaledBasis_det_apply b c hc v, D.volumeForm_eq_det b hb]

/-- **The metric-scaling law `vol (c • g) = c ^ (n / 2) • vol g`** as an equality of
top-dimensional alternating forms. -/
theorem volumeForm_smul_metric (b : OrthonormalBasis (Fin D.n) ℝ V)
    (hb : b.toBasis.orientation = D.orientation) (c : ℝ) (hc : 0 < c) :
    D.scaledVolumeForm b c hc = c ^ (D.n / 2 : ℝ) • D.volumeForm := by
  ext v
  rw [AlternatingMap.smul_apply, smul_eq_mul]
  exact D.scaledVolumeForm_apply b hb c hc v

/-- The rescaled volume form is the determinant in the rescaled basis (definitional form of the
explicit determinant interface). -/
theorem scaledVolumeForm_eq_det (b : OrthonormalBasis (Fin D.n) ℝ V) (c : ℝ) (hc : 0 < c) :
    D.scaledVolumeForm b c hc = (D.scaledBasis b c hc).det := rfl

/-- Scaling by `c = 1` does not change the volume form. -/
theorem scaledVolumeForm_one (b : OrthonormalBasis (Fin D.n) ℝ V) (hb : b.toBasis.orientation = D.orientation) :
    D.scaledVolumeForm b 1 (by norm_num) = D.volumeForm := by
  rw [D.volumeForm_smul_metric b hb 1 (by norm_num)]
  norm_num

end VolumeFormData

end Poincare.D7.Volume
