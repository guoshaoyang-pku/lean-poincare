import Poincare.D7.Curvature.Bridge
import Poincare.D7.Curvature.Example

/-!
# Poincare.D7.Curvature.Probe

**D7 Riemann curvature tensor layer, part 6: the mathlib API probe and the D7 API index.**

This module is a compilable probe. Every `#check` below must succeed against the pinned
toolchain, and every `#check_failure` must fail (recording a genuinely absent declaration).
The output of this file is the machine-checked record of the probe required by task item 1
("probe mathlib for existing curvature declarations and reuse them; do not redefine what
exists").

## Probe result (pinned mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`)

* **Present and reused**: `CovariantDerivative`, `CovariantDerivative.torsion`,
  `CovariantDerivative.torsion_antisymm`, `CovariantDerivative.IsMetricCompatible`,
  `CovariantDerivative.IsLeviCivitaConnection`,
  `CovariantDerivative.IsLeviCivitaConnection.uniqueness`,
  `CovariantDerivative.leviCivitaConnection`,
  `CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`,
  `CovariantDerivative.isMetricCompatible_leviCivitaConnection`,
  `CovariantDerivative.torsion_leviCivitaConnection_eq_zero`,
  `Bundle.RiemannianBundle`, `inner`, `LinearMap.trace`, `LinearMap.trace_smulRight`.
* **Absent**: `CovariantDerivative.curvature`, `RiemannTensor`, `RiemannianCurvature`,
  `RicciTensor`, `Bianchi`. The full-text search `grep -ri curvature Mathlib/` on the pinned
  checkout returns exactly one hit, a docstring in `MeasureTheory/Measure/Doubling.lean`.
  Consequently the D7 layer defines the curvature algebraically (reusing the D2
  `AbstractConnection.curvature`, which is not a mathlib declaration) and records the
  manifold-level construction as the blocked `Poincare.D7.Curvature.ManifoldCurvatureStatement`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

/-! ## 1. mathlib connection API: present and reused -/

#check CovariantDerivative
#check CovariantDerivative.torsion
#check CovariantDerivative.torsion_apply
#check CovariantDerivative.torsion_antisymm
#check CovariantDerivative.IsMetricCompatible
#check CovariantDerivative.IsLeviCivitaConnection
#check CovariantDerivative.IsLeviCivitaConnection.uniqueness
#check CovariantDerivative.leviCivitaConnection
#check CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
#check CovariantDerivative.isMetricCompatible_leviCivitaConnection
#check CovariantDerivative.torsion_leviCivitaConnection_eq_zero

/-! ## 2. mathlib metric and trace API: present and reused -/

#check Bundle.RiemannianBundle
#check Bundle.RiemannianMetric
#check inner
#check real_inner_self_nonneg
#check LinearMap.trace
#check LinearMap.trace_smulRight
#check LinearMap.trace_comp_comm
#check Module.finrank
#check Module.Basis

/-! ## 3. mathlib curvature API: absent (the probe records the gap) -/

#check_failure CovariantDerivative.curvature
#check_failure RiemannTensor
#check_failure RiemannianCurvature
#check_failure RicciTensor
#check_failure Bianchi
#check_failure CovariantDerivative.Curvature
#check_failure CovariantDerivative.ricci

/-! ## 4. The D7 API index -/

namespace Poincare
namespace D7
namespace Curvature

#check RiemannCurvatureData
#check RiemannCurvatureData.curvature
#check RiemannCurvatureData.curvatureForm
#check RiemannCurvatureData.curvatureForm_apply
#check RiemannCurvatureData.curvature_skew₁₂
#check RiemannCurvatureData.curvatureForm_skew₁₂
#check RiemannCurvatureData.curvatureForm_skew₃₄
#check RiemannCurvatureData.curvature_bianchi
#check RiemannCurvatureData.curvatureForm_bianchi
#check RiemannCurvatureData.curvatureForm_interchange
#check RiemannCurvatureData.curvatureForm_self₁
#check RiemannCurvatureData.curvatureForm_self₂
#check RiemannCurvatureData.curvatureForm_swap_pairs
#check RiemannCurvatureData.ricciForm
#check RiemannCurvatureData.ricciForm_eq_ricciOperator
#check RiemannCurvatureData.ricciForm_eq_sum_basis
#check RiemannCurvatureData.ricciForm_symm
#check RiemannCurvatureData.ricciEndo
#check RiemannCurvatureData.form_ricciEndo
#check RiemannCurvatureData.form_ricciEndo_symm
#check RiemannCurvatureData.scalarCurvature
#check RiemannCurvatureData.scalarCurvature_eq_sum_basis
#check RiemannCurvatureData.scalarCurvature_eq_d2
#check RiemannCurvatureData.gramForm
#check RiemannCurvatureData.IsNondegenerate2Plane
#check RiemannCurvatureData.gramForm_gl2
#check RiemannCurvatureData.isNondegenerate2Plane_gl2
#check RiemannCurvatureData.sectionalCurvature
#check RiemannCurvatureData.sectionalCurvature_swap
#check RiemannCurvatureData.sectionalCurvature_smul
#check RiemannCurvatureData.sectionalCurvature_smul_left
#check RiemannCurvatureData.sectionalCurvature_shear_left
#check RiemannCurvatureData.sectionalCurvature_gl2
#check RiemannCurvatureData.TwoPlane
#check RiemannCurvatureData.TwoPlane.sectionalCurvature
#check RiemannCurvatureData.TwoPlane.sectionalCurvature_congr
#check RiemannCurvatureData.zero
#check RiemannCurvatureData.mean
#check alternating_bilinear_apply

end Curvature
end D7
end Poincare

/-! ## 5. Bridges -/

#check Poincare.Longrun.Geometry.RiemannCurvatureTensor
#check Poincare.Longrun.Geometry.RiemannCurvatureTensor_first_pair_skew
#check Poincare.Longrun.Geometry.RiemannCurvatureTensor_bianchi
#check Poincare.Longrun.Geometry.RiemannCurvatureTensor_interchange
#check Poincare.Longrun.Geometry.RiemannCurvatureTensor_second_pair_skew
#check Probe.CurvatureTensor.toCurvatureOperator
#check Poincare.D7.Curvature.ricci_eq_probe_ricci

/-! ## 6. The blocked statements (explicit unproved `Prop`s, named blockers) -/

#check Poincare.D7.Curvature.ManifoldCurvatureStatement
#check Poincare.D7.Curvature.SecondBianchiStatement
#check Poincare.D7.Curvature.SecondBianchiIdentity
#check Poincare.D7.Curvature.CovariantDerivativeOfCurvature
#check Poincare.D7.Curvature.BlockerManifoldCurvature
#check Poincare.D7.Curvature.BlockerSecondBianchi

/-! ## 7. The concrete non-flat `so(3)` model (non-vacuity witness) -/

#check Poincare.D7.Curvature.So3.so3
#check Poincare.D7.Curvature.So3.crossBracket_compatible
#check Poincare.D7.Curvature.So3.so3_curvature_e0_e1_e1
#check Poincare.D7.Curvature.So3.so3_isNondegenerate2Plane_e0_e1
#check Poincare.D7.Curvature.So3.so3_sectionalCurvature_e0_e1
#check Poincare.D7.Curvature.So3.so3_sectionalCurvature_gl2_witness
#check Poincare.D7.Curvature.So3.so3_ricciForm_e0_e0
