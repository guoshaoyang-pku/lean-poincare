/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.Compat

/-!
# Task-local axiom audit (fail-closed)

This module is the *input* to the programmatic axiom audit: every new declaration of the
D12-volume-ibp layer is listed below together with its `#print axioms` cone. The
fail-closed audit script (task-local, run in `release/`) parses the `#print axioms` output
of this module and fails unless:

1. every listed declaration's axiom cone is contained in
   `{propext, Classical.choice, Quot.sound}`, and
2. the **negative control** `auditNegativeControl` (an intentionally declared, never-used
   axiom) IS flagged as unapproved — proving the detector actually fires on violations.

Allowed kernel axioms (the three standard ones; no `sorryAx`, `funext` is derivable and
not an axiom here):

```
propext, Classical.choice, Quot.sound
```

The negative control is isolated: no theorem or definition of the layer uses it (the
audit script verifies exactly that by checking the axiom cones of all real declarations).
-/


noncomputable section

namespace Poincare.D12.VolumeIBP.Audit

/-- **NEGATIVE CONTROL ONLY.** An intentionally unapproved axiom, never used by any
declaration of this layer. The audit script must flag it; if it did not, the detector
would be blind. Do not use in any proof. -/
axiom negativeControl : False

-- Basic.lean
#print axioms Poincare.D12.VolumeIBP.ChartMetric.matrix
#print axioms Poincare.D12.VolumeIBP.ChartMetric.g_symm
#print axioms Poincare.D12.VolumeIBP.ChartMetric.det_pos
#print axioms Poincare.D12.VolumeIBP.ChartMetric.density
#print axioms Poincare.D12.VolumeIBP.ChartMetric.density_pos
#print axioms Poincare.D12.VolumeIBP.ChartMetric.inner
#print axioms Poincare.D12.VolumeIBP.ChartMetric.inner_comm
#print axioms Poincare.D12.VolumeIBP.ChartMetric.inner_pos_of_ne_zero
#print axioms Poincare.D12.VolumeIBP.ChartMetric.invMatrix
#print axioms Poincare.D12.VolumeIBP.ChartMetric.invMatrix_mul
#print axioms Poincare.D12.VolumeIBP.ChartMetric.invMatrix_symm
#print axioms Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure
#print axioms Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric
#print axioms Poincare.D12.VolumeIBP.contDiff_if_const
-- Regularity.lean
#print axioms Poincare.D12.VolumeIBP.ChartMetric.det_contDiff
#print axioms Poincare.D12.VolumeIBP.ChartMetric.adjugate_entry_contDiff
#print axioms Poincare.D12.VolumeIBP.ChartMetric.invMatrix_entry_contDiff
#print axioms Poincare.D12.VolumeIBP.ChartMetric.density_contDiff
#print axioms Poincare.D12.VolumeIBP.ChartMetric.density_measurable
#print axioms Poincare.D12.VolumeIBP.ChartMetric.integral_riemannianMeasure_eq
#print axioms Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure_absolutelyContinuous
#print axioms Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure_univ
-- Divergence.lean
#print axioms Poincare.D12.VolumeIBP.exists_pi_Ioo_supset_compact
#print axioms Poincare.D12.VolumeIBP.ChartMetric.partialDeriv
#print axioms Poincare.D12.VolumeIBP.ChartMetric.weightedDivergence
#print axioms Poincare.D12.VolumeIBP.ChartMetric.divergence
#print axioms Poincare.D12.VolumeIBP.ChartMetric.weighted_divergence_integral_eq_zero
#print axioms Poincare.D12.VolumeIBP.ChartMetric.divergence_integral_eq_zero
-- IBP.lean
#print axioms Poincare.D12.VolumeIBP.ChartMetric.grad
#print axioms Poincare.D12.VolumeIBP.ChartMetric.laplacian
#print axioms Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse
#print axioms Poincare.D12.VolumeIBP.ChartMetric.driftLaplacian
#print axioms Poincare.D12.VolumeIBP.ChartMetric.partialDeriv_contDiff_one
#print axioms Poincare.D12.VolumeIBP.ChartMetric.grad_contDiff_one
#print axioms Poincare.D12.VolumeIBP.ChartMetric.grad_hasCompactSupport
#print axioms Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse_eq_sum
#print axioms Poincare.D12.VolumeIBP.ChartMetric.laplacian_continuous
#print axioms Poincare.D12.VolumeIBP.ChartMetric.laplacian_contDiff_two
#print axioms Poincare.D12.VolumeIBP.ChartMetric.weighted_divergence_mul_grad
#print axioms Poincare.D12.VolumeIBP.ChartMetric.chart_ibp
#print axioms Poincare.D12.VolumeIBP.ChartMetric.laplacian_integral_eq_zero
#print axioms Poincare.D12.VolumeIBP.ChartMetric.chart_ibp_laplacian
#print axioms Poincare.D12.VolumeIBP.ChartMetric.exp_neg_contDiff_one
#print axioms Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse_comm
#print axioms Poincare.D12.VolumeIBP.ChartMetric.weighted_divergence_mul_exp_grad
#print axioms Poincare.D12.VolumeIBP.ChartMetric.chart_weighted_ibp
#print axioms Poincare.D12.VolumeIBP.ChartMetric.driftLaplacian_continuous
-- ChangeOfVariables.lean
#print axioms Poincare.D12.VolumeIBP.ChartDiffeomorphism
#print axioms Poincare.D12.VolumeIBP.ChartMetric.jacobianMatrix
#print axioms Poincare.D12.VolumeIBP.ChartMetric.pullbackMatrix
#print axioms Poincare.D12.VolumeIBP.ChartMetric.jacobianMatrix_det
#print axioms Poincare.D12.VolumeIBP.ChartMetric.det_pullbackMatrix
#print axioms Poincare.D12.VolumeIBP.ChartMetric.jentry_contDiff
#print axioms Poincare.D12.VolumeIBP.ChartMetric.jacobianMatrix_mulVec_eq_fderiv
#print axioms Poincare.D12.VolumeIBP.ChartMetric.inner_grad_eq_gradInnerInverse
#print axioms Poincare.D12.VolumeIBP.ChartMetric.pullbackMetric
#print axioms Poincare.D12.VolumeIBP.ChartMetric.pullbackDensity_eq
#print axioms Poincare.D12.VolumeIBP.ChartMetric.pullback_measure_naturality
-- Example.lean
#print axioms Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric_density_one
#print axioms Poincare.D12.VolumeIBP.ChartMetric.expMetricOne
#print axioms Poincare.D12.VolumeIBP.ChartMetric.expMetricOne_density_eq
#print axioms Poincare.D12.VolumeIBP.ChartMetric.chart_ibp_euclidean_one
-- Blocked.lean
#print axioms Poincare.D12.VolumeIBP.chartWeightedIBPStatementRestricted_holds
-- the negative control itself (expected to be flagged)
#print axioms Poincare.D12.VolumeIBP.Audit.negativeControl

end Poincare.D12.VolumeIBP.Audit
