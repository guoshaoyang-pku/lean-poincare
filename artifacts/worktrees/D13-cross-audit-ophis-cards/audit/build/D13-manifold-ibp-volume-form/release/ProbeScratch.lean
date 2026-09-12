import Mathlib
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Algebra.Support

open scoped BigOperators
open MeasureTheory

-- 1. determinant continuity for matrix-valued functions
#check Continuous.matrix_det
#check Matrix.GeneralLinearGroup.continuous_det
#check Matrix.PosDef.eigenvalues_pos
#check Matrix.PosDef.det_pos
#check Matrix.posDef_diagonal_iff
#check Matrix.IsHermitian.det_eq_prod_eigenvalues

-- 2. withDensity and Bochner integral translation
-- (declared at ROOT namespace in MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean,
-- after `end ContinuousLinearMap` — not under MeasureTheory)
#check integral_withDensity_eq_integral_smul
#check integral_withDensity_eq_integral_smul₀
#check Measure.withDensity
#check MeasureTheory.lintegral_withDensity_eq_lintegral_mul
#check setIntegral_withDensity_eq_setIntegral_smul₀

-- 3. divergence theorem
#check MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
#check MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
#check MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv
#check BoxIntegral.Box.Ioo
#check BoxIntegral.Box.Icc

-- 4. change of variables
#check MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
#check MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul
#check MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
#check MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
#check OpenPartialHomeomorph

-- 5. compact support
#check HasCompactSupport
#check tsupport
#check Function.support
-- `isCompact_tsupport` does not exist at this revision; compactness of tsupport is
-- the defining content of `HasCompactSupport` (closure of support is compact)
#check hasCompactSupport_iff_eventuallyEq
#check HasCompactSupport.mul_left
#check HasCompactSupport.mul_right

-- 6. orientation / volume form API (vector-space level)
#check Orientation
#check Orientation.volumeForm
#check Orientation.volumeForm_robust
#check Orientation.volumeForm_neg_orientation
#check Measure.addHaar
#check Measure.IsAddHaarMeasure

-- 7. linear map det bridges
#check Matrix.toLin'
#check LinearMap.det_toLin'
#check LinearMap.det
#check ContinuousLinearMap.det

-- 8. sqrt lemmas
#check Real.sqrt_mul
#check Real.sqrt_sq_eq_abs
#check Real.sqrt_pos
#check Real.sqrt_nonneg

-- 9. smoothness
#check ContDiff
#check fderiv
#check HasFDerivAt
#check Continuous.matrix_det

-- 10. inverse matrix
#check Matrix.inv_def
#check Matrix.mul_nonsing_inv
#check Matrix.nonsing_inv_mul
#check Matrix.inv_mul_of_invertible
#check Matrix.det_nonsing_inv

-- 11. EuclideanSpace APIs
#check EuclideanSpace.equiv
#check EuclideanSpace.single
#check EuclideanSpace.inner_eq_star_dotProduct

-- 12. basis / dot product
#check Pi.single
#check dotProduct
#check Matrix.mulVec
#check Matrix.vecMul

-- 13. measurability
-- `Measurable.matrix_det` does not exist at this revision; measurability of the
-- determinant follows from Continuous.matrix_det + Continuous.measurable
#check Continuous.matrix_det
#check Continuous.measurable
#check AEMeasurable
#check Measurable.comp_aemeasurable
