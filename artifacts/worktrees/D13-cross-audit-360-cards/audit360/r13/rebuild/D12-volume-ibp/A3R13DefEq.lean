-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.VolumeIBP
import Poincare.D12.VolumeIBP.Audit
import Poincare.D12.VolumeIBP.Basic
import Poincare.D12.VolumeIBP.Blocked
import Poincare.D12.VolumeIBP.ChangeOfVariables
import Poincare.D12.VolumeIBP.Compat
import Poincare.D12.VolumeIBP.Divergence
import Poincare.D12.VolumeIBP.Example
import Poincare.D12.VolumeIBP.IBP
import Poincare.D12.VolumeIBP.Regularity

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.VolumeIBP.ChartDiffeomorphism,
  ``Poincare.D12.VolumeIBP.ChartMetric.adjugate_entry_contDiff,
  ``Poincare.D12.VolumeIBP.ChartMetric.chart_ibp,
  ``Poincare.D12.VolumeIBP.ChartMetric.chart_ibp_euclidean_one,
  ``Poincare.D12.VolumeIBP.ChartMetric.chart_ibp_laplacian,
  ``Poincare.D12.VolumeIBP.ChartMetric.chart_ibp_self,
  ``Poincare.D12.VolumeIBP.ChartMetric.chart_weighted_ibp,
  ``Poincare.D12.VolumeIBP.ChartMetric.density,
  ``Poincare.D12.VolumeIBP.ChartMetric.densityNNReal,
  ``Poincare.D12.VolumeIBP.ChartMetric.densityNNReal_eq,
  ``Poincare.D12.VolumeIBP.ChartMetric.densityNNReal_measurable,
  ``Poincare.D12.VolumeIBP.ChartMetric.density_aemeasurable,
  ``Poincare.D12.VolumeIBP.ChartMetric.density_contDiff,
  ``Poincare.D12.VolumeIBP.ChartMetric.density_continuous,
  ``Poincare.D12.VolumeIBP.ChartMetric.density_measurable,
  ``Poincare.D12.VolumeIBP.ChartMetric.density_ne_zero,
  ``Poincare.D12.VolumeIBP.ChartMetric.density_pos,
  ``Poincare.D12.VolumeIBP.ChartMetric.det_contDiff,
  ``Poincare.D12.VolumeIBP.ChartMetric.det_pos,
  ``Poincare.D12.VolumeIBP.ChartMetric.det_pullbackMatrix,
  ``Poincare.D12.VolumeIBP.ChartMetric.divergence,
  ``Poincare.D12.VolumeIBP.ChartMetric.divergence_integral_eq_zero,
  ``Poincare.D12.VolumeIBP.ChartMetric.divergence_integral_eq_zero_density,
  ``Poincare.D12.VolumeIBP.ChartMetric.driftLaplacian,
  ``Poincare.D12.VolumeIBP.ChartMetric.driftLaplacian_continuous,
  ``Poincare.D12.VolumeIBP.ChartMetric.entry_contDiff,
  ``Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric,
  ``Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric_density_one,
  ``Poincare.D12.VolumeIBP.ChartMetric.expMetricOne,
  ``Poincare.D12.VolumeIBP.ChartMetric.expMetricOne_density_eq,
  ``Poincare.D12.VolumeIBP.ChartMetric.exp_neg_contDiff_one,
  ``Poincare.D12.VolumeIBP.ChartMetric.g_symm,
  ``Poincare.D12.VolumeIBP.ChartMetric.grad,
  ``Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse,
  ``Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse_comm,
  ``Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse_continuous,
  ``Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse_eq_sum,
  ``Poincare.D12.VolumeIBP.ChartMetric.grad_contDiff_one,
  ``Poincare.D12.VolumeIBP.ChartMetric.grad_hasCompactSupport,
  ``Poincare.D12.VolumeIBP.ChartMetric.hasCompactSupport_partialDeriv,
  ``Poincare.D12.VolumeIBP.ChartMetric.inner,
  ``Poincare.D12.VolumeIBP.ChartMetric.inner_comm,
  ``Poincare.D12.VolumeIBP.ChartMetric.inner_grad_eq_gradInnerInverse,
  ``Poincare.D12.VolumeIBP.ChartMetric.inner_pos_of_ne_zero,
  ``Poincare.D12.VolumeIBP.ChartMetric.integral_riemannianMeasure_eq,
  ``Poincare.D12.VolumeIBP.ChartMetric.invMatrix,
  ``Poincare.D12.VolumeIBP.ChartMetric.invMatrix_entry_contDiff,
  ``Poincare.D12.VolumeIBP.ChartMetric.invMatrix_mul,
  ``Poincare.D12.VolumeIBP.ChartMetric.invMatrix_mul_matrix_mul_invMatrix,
  ``Poincare.D12.VolumeIBP.ChartMetric.invMatrix_symm,
  ``Poincare.D12.VolumeIBP.ChartMetric.jacobianMatrix,
  ``Poincare.D12.VolumeIBP.ChartMetric.jacobianMatrix_det,
  ``Poincare.D12.VolumeIBP.ChartMetric.jacobianMatrix_mulVec_eq_fderiv,
  ``Poincare.D12.VolumeIBP.ChartMetric.jentry_contDiff,
  ``Poincare.D12.VolumeIBP.ChartMetric.laplacian,
  ``Poincare.D12.VolumeIBP.ChartMetric.laplacian_contDiff_two,
  ``Poincare.D12.VolumeIBP.ChartMetric.laplacian_continuous,
  ``Poincare.D12.VolumeIBP.ChartMetric.laplacian_integral_eq_zero,
  ``Poincare.D12.VolumeIBP.ChartMetric.matrix,
  ``Poincare.D12.VolumeIBP.ChartMetric.matrix_mul_invMatrix,
  ``Poincare.D12.VolumeIBP.ChartMetric.metricInnerInverse,
  ``Poincare.D12.VolumeIBP.ChartMetric.partialDeriv,
  ``Poincare.D12.VolumeIBP.ChartMetric.partialDeriv_contDiff_one,
  ``Poincare.D12.VolumeIBP.ChartMetric.pullbackDensity_eq,
  ``Poincare.D12.VolumeIBP.ChartMetric.pullbackMatrix,
  ``Poincare.D12.VolumeIBP.ChartMetric.pullbackMetric,
  ``Poincare.D12.VolumeIBP.ChartMetric.pullback_measure_naturality,
  ``Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure,
  ``Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure_absolutelyContinuous,
  ``Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure_univ,
  ``Poincare.D12.VolumeIBP.ChartMetric.setIntegral_riemannianMeasure_eq,
  ``Poincare.D12.VolumeIBP.ChartMetric.weightedDivergence,
  ``Poincare.D12.VolumeIBP.ChartMetric.weighted_divergence_integral_eq_zero,
  ``Poincare.D12.VolumeIBP.ChartMetric.weighted_divergence_mul_exp_grad,
  ``Poincare.D12.VolumeIBP.ChartMetric.weighted_divergence_mul_grad,
  ``Poincare.D12.VolumeIBP.chartWeightedIBPStatementRestricted_holds,
  ``Poincare.D12.VolumeIBP.contDiff_if_const,
  ``Poincare.D12.VolumeIBP.exists_pi_Ioo_supset_compact]

/-- Only theorems with a Prop-valued hypothesis can commit the
assumption-as-conclusion defect; a plain function whose argument type equals
its result type (e.g. `def f (x : R) : R`) is benign. -/
def run : CommandElabM Unit := do
  liftTermElabM do
    let mut checked := 0
    for n in claimed do
      let ci ← getConstInfo n
      unless ci matches .thmInfo _ do continue
      checked := checked + 1
      Lean.Meta.forallTelescope ci.type (fun args body => do
        if ← isDefEq body (.const ``True []) then
          logInfo m!"A3R13D|TRIVIAL_TRUE|{n}"
        for a in args do
          let ty ← inferType a
          if ← isProp ty then
            if ← isDefEq ty body then
              let u := a.fvarId!.name
              logInfo m!"A3R13D|HYP_DEFEQ|{n}|{u}"
        )
    logInfo m!"A3R13D|CHECKED|{checked}"
  logInfo m!"A3R13D|DONE"

end A3R13D
run_cmd A3R13D.run
