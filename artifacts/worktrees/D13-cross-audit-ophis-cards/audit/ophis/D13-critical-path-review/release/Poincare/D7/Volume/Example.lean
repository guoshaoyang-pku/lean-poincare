/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Poincare.D7.Volume.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Volume.Example

**D7 orientability and volume-form algebra layer, part 4: concrete non-vacuity witnesses.**

The general theory of `Poincare.D7.Volume.Basic`–`Poincare.D7.Volume.Scaling` is instantiated on
the Euclidean spaces `EuclideanSpace ℝ (Fin n)`, with the standard orthonormal basis
`EuclideanSpace.basisFun`. The kernel-checked values below show that the definitions are not
vacuous:

* on `EuclideanSpace ℝ (Fin 1)`, the volume form is the identity on coordinates;
* on `EuclideanSpace ℝ (Fin 2)`, the volume form on the standard basis is the `2 × 2`
  determinant `x 0 * y 1 - x 1 * y 0`;
* the metric-rescaling law with `c = 4` gives the factor `4` in dimension `2`
  (`4 ^ (2 / 2) = 4`);
* reversing the orientation changes the sign, so the reversed volume form on the standard basis
  is `-1`;
* the endomorphism `x ↦ 2 • x` multiplies the volume form by its determinant `4` (concrete
  change-of-variables instance).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

noncomputable section

open Module

namespace Poincare.D7.Volume

/-- The standard volume-form datum on `EuclideanSpace ℝ (Fin n)`: the orientation of the
standard orthonormal basis `EuclideanSpace.basisFun`. -/
noncomputable abbrev euclideanVolumeFormData (n : ℕ) :
    VolumeFormData (EuclideanSpace ℝ (Fin n)) where
  n := n
  finrank_eq := finrank_euclideanSpace_fin
  orientation := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation

@[simp]
theorem euclideanVolumeFormData_n (n : ℕ) : (euclideanVolumeFormData n).n = n := rfl

/-- The explicit determinant interface for the standard Euclidean datum: the volume form is the
determinant in the standard orthonormal basis. -/
theorem euclideanVolumeFormData_volumeForm_eq_det (n : ℕ) :
    (euclideanVolumeFormData n).volumeForm =
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det :=
  (euclideanVolumeFormData n).volumeForm_eq_det (EuclideanSpace.basisFun (Fin n) ℝ) rfl

/-- On `EuclideanSpace ℝ (Fin 1)` the volume form is evaluation of the single coordinate. -/
theorem euclideanVolumeFormData_one_apply (v : Fin 1 → EuclideanSpace ℝ (Fin 1)) :
    (euclideanVolumeFormData 1).volumeForm v = v 0 0 := by
  have hdet : (euclideanVolumeFormData 1).volumeForm =
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.det :=
    euclideanVolumeFormData_volumeForm_eq_det 1
  rw [hdet, Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- On `EuclideanSpace ℝ (Fin 2)` the volume form is the `2 × 2` determinant
`v 0 0 * v 1 1 - v 0 1 * v 1 0`. -/
theorem euclideanVolumeFormData_two_apply (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    (euclideanVolumeFormData 2).volumeForm v = v 0 0 * v 1 1 - v 0 1 * v 1 0 := by
  have hdet : (euclideanVolumeFormData 2).volumeForm =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det :=
    euclideanVolumeFormData_volumeForm_eq_det 2
  rw [hdet, Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply,
    Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_repr]
  ring

/-- The volume form of the standard datum evaluated on the standard basis is `1`. -/
theorem euclideanVolumeFormData_apply_basis (n : ℕ) :
    (euclideanVolumeFormData n).volumeForm (EuclideanSpace.basisFun (Fin n) ℝ) = 1 :=
  (euclideanVolumeFormData n).volumeForm_apply_basis (EuclideanSpace.basisFun (Fin n) ℝ) rfl

/-- **Concrete metric-rescaling witness.** In dimension `2`, rescaling the metric by `c = 4`
multiplies the volume form by `4 ^ (2 / 2) = 4`. -/
theorem euclideanVolumeFormData_scaling_witness (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    (euclideanVolumeFormData 2).scaledVolumeForm (EuclideanSpace.basisFun (Fin 2) ℝ) 4
        (by norm_num) v =
      4 * (euclideanVolumeFormData 2).volumeForm v := by
  have h := (euclideanVolumeFormData 2).scaledVolumeForm_apply
    (EuclideanSpace.basisFun (Fin 2) ℝ) rfl 4 (by norm_num) v
  rw [h]
  norm_num

/-- **Concrete orientation-reversal witness.** On the standard basis of
`EuclideanSpace ℝ (Fin 2)`, the reversed-orientation volume form takes the value `-1`. -/
theorem euclideanVolumeFormData_reverse_apply_basis :
    (euclideanVolumeFormData 2).reverse.volumeForm (EuclideanSpace.basisFun (Fin 2) ℝ) = -1 := by
  have h := VolumeFormData.reverse_volumeForm (euclideanVolumeFormData 2)
  have h' : (euclideanVolumeFormData 2).reverse.volumeForm (EuclideanSpace.basisFun (Fin 2) ℝ)
      = -((euclideanVolumeFormData 2).volumeForm (EuclideanSpace.basisFun (Fin 2) ℝ)) := by
    rw [h]
    rfl
  rw [h', euclideanVolumeFormData_apply_basis]

/-- **Concrete change-of-variables witness.** The endomorphism `x ↦ 2 • x` has determinant
`2 ^ 2 = 4` in dimension `2`, so it multiplies the volume form by `4`. -/
theorem euclideanVolumeFormData_changeOfVariables_witness
    (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    (euclideanVolumeFormData 2).volumeForm
        (((2 : ℝ) • (1 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))) ∘ v) =
      4 * (euclideanVolumeFormData 2).volumeForm v := by
  have h := (euclideanVolumeFormData 2).volumeForm_comp_linearMap
    (EuclideanSpace.basisFun (Fin 2) ℝ) rfl
    ((2 : ℝ) • (1 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))) v
  rw [h, LinearMap.det_smul, show (1 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) =
    LinearMap.id from rfl, LinearMap.det_id, mul_one]
  norm_num [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 from finrank_euclideanSpace_fin]

end Poincare.D7.Volume
