/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Poincare.D7.Volume.Blocked
import Poincare.D7.Volume.Example

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Volume.Probe

**D7 orientability and volume-form algebra layer, part 6: the mathlib API probe and the D7 API
index.**

This module is a compilable probe. Every `#check` below must succeed against the pinned
toolchain, and every `#check_failure` must fail (recording a genuinely absent declaration). The
output of this file is the machine-checked record of the probe required by the task.

## Probe result (pinned mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`)

* **Present and reused**: `Orientation`, `Orientation.volumeForm`,
  `Orientation.volumeForm_robust`, `Orientation.volumeForm_robust_neg`,
  `Orientation.volumeForm_neg_orientation`, `Orientation.volumeForm_map`,
  `Orientation.volumeForm_comp_linearIsometryEquiv`,
  `Orientation.abs_volumeForm_apply_of_orthonormal`, `OrthonormalBasis`,
  `OrthonormalBasis.adjustToOrientation`, `stdOrthonormalBasis`,
  `AlternatingMap.map_smul_univ`, `Module.Basis.det`, `Module.Basis.det_comp`,
  `Module.Basis.det_unitsSMul`, `Module.Basis.unitsSMul`, `Module.Basis.orientation_unitsSMul`,
  `Module.Ray.units_smul_of_pos`, `LinearMap.det_smul`, `LinearMap.det_comp`,
  `Measure.map_linearMap_addHaar_eq_smul_addHaar`, `Measure.addHaar_preimage_linearMap`,
  `Measure.addHaar_image_linearMap`, `ContMDiffSection`, `RiemannianBundle`,
  `IsRiemannianManifold`, `IsContMDiffRiemannianBundle`, `TangentSpace`, `ModelWithCorners`,
  `IsManifold`.
* **Absent**: `Manifold.Orientation`, `IsManifold.Orientable`, `Orientable`,
  `RiemannianVolumeForm`, `RiemannianVolumeMeasure`, `Bundle.AlternatingMap`,
  `RiemannianDensity`. The manifold-level volume form and its smoothness are therefore the
  blocked `Prop`s of `Poincare.D7.Volume.Blocked`, with the exact missing dependencies listed
  there.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Bundle Module MeasureTheory

open Poincare.D7.Volume

/-! ## 1. mathlib orientation and volume-form API: present and reused -/

#check Orientation
#check Orientation.volumeForm
#check Orientation.volumeForm_robust
#check Orientation.volumeForm_robust_neg
#check Orientation.volumeForm_neg_orientation
#check Orientation.volumeForm_map
#check Orientation.volumeForm_comp_linearIsometryEquiv
#check Orientation.abs_volumeForm_apply_of_orthonormal
#check Orientation.map
#check Orientation.map_eq_iff_det_pos
#check Orientation.map_eq_neg_iff_det_neg
#check OrthonormalBasis
#check OrthonormalBasis.toBasis
#check OrthonormalBasis.adjustToOrientation
#check stdOrthonormalBasis
#check orthonormal_iff_ite

/-! ## 2. mathlib determinant interface: present and reused -/

#check AlternatingMap.map_smul_univ
#check Module.Basis.det
#check Module.Basis.det_apply
#check Module.Basis.det_self
#check Module.Basis.det_comp
#check Module.Basis.det_unitsSMul
#check Module.Basis.unitsSMul
#check Module.Basis.unitsSMul_apply
#check Module.Basis.orientation_unitsSMul
#check Module.Basis.orientation_eq_iff_det_pos
#check Module.Ray.units_smul_of_pos
#check LinearMap.det_smul
#check LinearMap.det_comp
#check LinearMap.det_conj

/-! ## 3. mathlib finite-dimensional measure-theoretic change of variables: present and reused -/

#check Measure.map_linearMap_addHaar_eq_smul_addHaar
#check Measure.addHaar_preimage_linearMap
#check Measure.addHaar_image_linearMap
#check Measure.addHaar
#check Measure.IsAddHaarMeasure
#check lintegral_map
#check lintegral_smul_measure

/-! ## 4. mathlib manifold Riemannian API: present and reused by the blocked statements -/

#check ModelWithCorners
#check IsManifold
#check TangentSpace
#check RiemannianBundle
#check IsRiemannianManifold
#check IsContMDiffRiemannianBundle
#check ContMDiffSection
#check FiberBundle
#check VectorBundle
#check ContMDiffVectorBundle
#check tangentSpaceCastModel

/-! ## 5. absent at the pinned revision (recorded by `#check_failure`) -/

#check_failure Manifold.Orientation
#check_failure IsManifold.Orientable
#check_failure Orientable
#check_failure RiemannianVolumeForm
#check_failure RiemannianVolumeMeasure
#check_failure Bundle.AlternatingMap
#check_failure RiemannianDensity
#check_failure OrientableManifold

/-! ## 6. D7 API index -/

#check VolumeFormData
#check VolumeFormData.volumeForm
#check VolumeFormData.volumeForm_eq_det
#check VolumeFormData.volumeForm_eq_neg_det_of_orientation_ne
#check VolumeFormData.reverse
#check VolumeFormData.reverse_volumeForm
#check VolumeFormData.volumeForm_comp_linearIsometryEquiv_of_det_pos
#check VolumeFormData.volumeForm_comp_linearIsometryEquiv_of_det_neg
#check VolumeFormData.std
#check sqrtInvUnit
#check sqrt_pow_eq_rpow_half
#check VolumeFormData.scaledBasis
#check VolumeFormData.scaledBasis_orthonormal
#check VolumeFormData.scaledBasis_orientation
#check VolumeFormData.scaledBasis_det_apply
#check VolumeFormData.scaledVolumeForm
#check VolumeFormData.scaledVolumeForm_apply
#check VolumeFormData.volumeForm_smul_metric
#check VolumeFormData.volumeForm_comp_linearMap
#check lintegral_comp_linearMap_eq
#check lintegral_linearMap_eq
#check map_linearMap_eq_smul_addHaar
#check addHaar_preimage_linearMap'
#check addHaar_image_linearMap'
#check RiemannianVolumeFormExistsStatement
#check RiemannianVolumeFormSmoothStatement
#check RiemannianVolumeMeasureStatement
#check MissingMathlibDependencies
#check euclideanVolumeFormData
#check euclideanVolumeFormData_two_apply
#check euclideanVolumeFormData_scaling_witness
