import Poincare.D7.Curvature.Bridge
import Poincare.D7.Curvature.Example

/-!
# Poincare.D7.Curvature.Audit

**D7 Riemann curvature tensor layer, part 7: the per-declaration axiom audit.**

This module runs `#print axioms` on every principal declaration of the D7 layer. The expected
cones are `{}`, `{propext}`, `{propext, Quot.sound}` or
`{propext, Classical.choice, Quot.sound}`; the only axioms permitted by the task are
`propext`, `Classical.choice` and `Quot.sound`. In particular, no declaration may depend on
`sorryAx`, and none of the D7 sources contains `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted`.

The blocked statements are `def ... : Prop` with no proof; `#print axioms` on them reports the
axioms used by the *statement*, which is the audit of the interface (no hidden assumption).
-/

open scoped BigOperators

/-! ## The data structure and the two tensors -/

#print axioms Poincare.D7.Curvature.RiemannCurvatureData
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvature
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.toCurvatureOperator
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.zero
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.mean

/-! ## Symmetries -/

#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvature_skew₁₂
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_skew₁₂
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvature_bianchi
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_bianchi
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.form_comp_sub_skew
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_skew₃₄
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_interchange
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_self₁
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_self₂
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_swap_pairs

/-! ## Ricci and scalar curvature -/

#print axioms Poincare.D7.Curvature.RiemannCurvatureData.ricciForm
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.ricciForm_eq_ricciOperator
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.ricciForm_eq_sum_basis
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.ricciForm_symm
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.ricciEndo
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.form_ricciEndo
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.form_ricciEndo_symm
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.scalarCurvature
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.scalarCurvature_eq_sum_basis
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.scalarCurvature_eq_d2

/-! ## Sectional curvature -/

#print axioms Poincare.D7.Curvature.RiemannCurvatureData.gramForm
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.gramForm_gl2
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.isNondegenerate2Plane_gl2
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.sectionalCurvature
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.sectionalCurvature_swap
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.sectionalCurvature_smul
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.sectionalCurvature_shear_left
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.sectionalCurvature_gl2
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.TwoPlane.sectionalCurvature_congr

/-! ## The generic algebra lemma -/

#print axioms Poincare.D7.Curvature.alternating_bilinear_apply

/-! ## The acceptance-named bridges -/

#print axioms Poincare.Longrun.Geometry.RiemannCurvatureTensor
#print axioms Poincare.Longrun.Geometry.RiemannCurvatureTensor_first_pair_skew
#print axioms Poincare.Longrun.Geometry.RiemannCurvatureTensor_bianchi
#print axioms Poincare.Longrun.Geometry.RiemannCurvatureTensor_interchange
#print axioms Poincare.Longrun.Geometry.RiemannCurvatureTensor_second_pair_skew
#print axioms Probe.CurvatureTensor.toCurvatureOperator
#print axioms Poincare.D7.Curvature.ricci_eq_probe_ricci

/-! ## The blocked statements and their named blockers -/

#print axioms Poincare.D7.Curvature.ManifoldCurvatureStatement
#print axioms Poincare.D7.Curvature.SecondBianchiStatement
#print axioms Poincare.D7.Curvature.CovariantDerivativeOfCurvature
#print axioms Poincare.D7.Curvature.BlockerManifoldCurvature_ne_nil
#print axioms Poincare.D7.Curvature.BlockerSecondBianchi_ne_nil

/-! ## The concrete non-flat `so(3)` model (non-vacuity witness) -/

#print axioms Poincare.D7.Curvature.So3.stdForm
#print axioms Poincare.D7.Curvature.So3.stdMetric
#print axioms Poincare.D7.Curvature.So3.crossBracket
#print axioms Poincare.D7.Curvature.So3.crossBracket_compatible
#print axioms Poincare.D7.Curvature.So3.so3
#print axioms Poincare.D7.Curvature.So3.so3_curvature_e0_e1_e1
#print axioms Poincare.D7.Curvature.So3.so3_gramForm_e0_e1
#print axioms Poincare.D7.Curvature.So3.so3_isNondegenerate2Plane_e0_e1
#print axioms Poincare.D7.Curvature.So3.so3_sectionalCurvature_e0_e1
#print axioms Poincare.D7.Curvature.So3.so3_sectionalCurvature_gl2_witness
#print axioms Poincare.D7.Curvature.So3.so3_ricciForm_e0_e0
