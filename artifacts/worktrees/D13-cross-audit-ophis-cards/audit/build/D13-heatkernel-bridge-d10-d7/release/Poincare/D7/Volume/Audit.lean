/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Poincare.D7.Volume.Probe

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Volume.Audit

**D7 orientability and volume-form algebra layer, part 7: the `#print axioms` audit.**

This module runs `#print axioms` on every principal declaration of the D7 volume-form layer. It
compiles (exit 0) and the expected output is the single cone

```
'<declaration>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

for every entry, with no `sorryAx`, `native_decide`, `proof_wanted`, or any other unapproved
axiom.
-/

open Poincare.D7.Volume

/-! ## Basic: the datum, the volume form, the determinant interface, orientation reversal -/

#print axioms VolumeFormData
#print axioms VolumeFormData.volumeForm
#print axioms VolumeFormData.volumeForm_def
#print axioms VolumeFormData.volumeForm_eq_det
#print axioms VolumeFormData.volumeForm_eq_neg_det_of_orientation_ne
#print axioms VolumeFormData.volumeForm_apply_basis
#print axioms VolumeFormData.abs_volumeForm_apply_of_orthonormal
#print axioms VolumeFormData.reverse
#print axioms VolumeFormData.reverse_volumeForm
#print axioms VolumeFormData.volumeForm_comp_linearIsometryEquiv_of_det_pos
#print axioms VolumeFormData.volumeForm_comp_linearIsometryEquiv_of_det_neg
#print axioms VolumeFormData.std
#print axioms VolumeFormData.std_volumeForm_eq_det

/-! ## Scaling: the metric-scaling law `vol (c • g) = c ^ (n / 2) • vol g` -/

#print axioms sqrtInvUnit
#print axioms sqrtInvUnit_val
#print axioms sqrtInvUnit_pos
#print axioms sqrt_pow_eq_rpow_half
#print axioms VolumeFormData.scaledBasis
#print axioms VolumeFormData.scaledBasis_apply
#print axioms VolumeFormData.scaledBasis_orthonormal
#print axioms VolumeFormData.scaledBasis_orientation
#print axioms VolumeFormData.scaledBasis_det_apply
#print axioms VolumeFormData.scaledVolumeForm
#print axioms VolumeFormData.scaledVolumeForm_apply
#print axioms VolumeFormData.volumeForm_smul_metric
#print axioms VolumeFormData.scaledVolumeForm_eq_det
#print axioms VolumeFormData.scaledVolumeForm_one

/-! ## Change of variables for linear maps with nonzero determinant -/

#print axioms VolumeFormData.volumeForm_comp_linearMap
#print axioms VolumeFormData.volumeForm_comp_linearMap_ne_zero
#print axioms lintegral_comp_linearMap_eq
#print axioms lintegral_linearMap_eq
#print axioms map_linearMap_eq_smul_addHaar
#print axioms addHaar_preimage_linearMap'
#print axioms addHaar_image_linearMap'

/-! ## Concrete Euclidean witnesses -/

#print axioms euclideanVolumeFormData
#print axioms euclideanVolumeFormData_n
#print axioms euclideanVolumeFormData_volumeForm_eq_det
#print axioms euclideanVolumeFormData_one_apply
#print axioms euclideanVolumeFormData_two_apply
#print axioms euclideanVolumeFormData_apply_basis
#print axioms euclideanVolumeFormData_scaling_witness
#print axioms euclideanVolumeFormData_reverse_apply_basis
#print axioms euclideanVolumeFormData_changeOfVariables_witness

/-! ## Blocked statements and named blockers -/

#print axioms BlockerRiemannianVolumeForm
#print axioms BlockerManifoldMeasureTheory
#print axioms BlockerManifoldOrientation
#print axioms BlockerRiemannianVolumeForm_ne_nil
#print axioms BlockerManifoldMeasureTheory_ne_nil
#print axioms BlockerManifoldOrientation_ne_nil
#print axioms finrank_tangentSpace
#print axioms tangentVolumeForm
#print axioms TopFormBundle
#print axioms IsOrientationVolumeForm
#print axioms RiemannianVolumeFormExistsStatement
#print axioms RiemannianVolumeFormSmoothStatement
#print axioms RiemannianVolumeMeasureStatement
#print axioms MissingMathlibDependencies
#print axioms MissingMathlibDependencies_ne_nil
#print axioms MissingMathlibDependencies_length
