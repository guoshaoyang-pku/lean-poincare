-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.SpectralSobolev.All
import Poincare.D12.SpectralSobolev.AxiomAudit
import Poincare.D12.SpectralSobolev.Basic
import Poincare.D12.SpectralSobolev.Examples
import Poincare.D12.SpectralSobolev.HeatConvergence
import Poincare.D12.SpectralSobolev.Poincare
import Poincare.D12.SpectralSobolev.Semigroup

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.SpectralSobolev.fourierCoeffOn_deriv_periodic,
  ``Poincare.D12.SpectralSobolev.fourierCoeffOn_zero_eq_mean,
  ``Poincare.D12.SpectralSobolev.fourierCoeff_heatEvolve,
  ``Poincare.D12.SpectralSobolev.heatCoeffs,
  ``Poincare.D12.SpectralSobolev.heatCoeffsL2,
  ``Poincare.D12.SpectralSobolev.heatCoeffs_apply,
  ``Poincare.D12.SpectralSobolev.heatEvolve,
  ``Poincare.D12.SpectralSobolev.heatEvolve_add,
  ``Poincare.D12.SpectralSobolev.heatEvolve_fourierLp,
  ``Poincare.D12.SpectralSobolev.heatEvolve_norm_le,
  ``Poincare.D12.SpectralSobolev.heatEvolve_tendsto_self,
  ``Poincare.D12.SpectralSobolev.heatEvolve_zero,
  ``Poincare.D12.SpectralSobolev.heatSeries_hasSum,
  ``Poincare.D12.SpectralSobolev.heatWeight,
  ``Poincare.D12.SpectralSobolev.heatWeight_abs_le_one,
  ``Poincare.D12.SpectralSobolev.heatWeight_le_one,
  ``Poincare.D12.SpectralSobolev.heatWeight_lt_one_of_pos,
  ``Poincare.D12.SpectralSobolev.heatWeight_nonneg,
  ``Poincare.D12.SpectralSobolev.heatWeight_pos,
  ``Poincare.D12.SpectralSobolev.heatWeight_tendsto_one,
  ``Poincare.D12.SpectralSobolev.heatWeight_zero,
  ``Poincare.D12.SpectralSobolev.heat_evolution_first_mode_nontrivial,
  ``Poincare.D12.SpectralSobolev.integral_cos_sq_period,
  ``Poincare.D12.SpectralSobolev.integral_sin_sq_period,
  ``Poincare.D12.SpectralSobolev.norm_cos_le_one,
  ``Poincare.D12.SpectralSobolev.norm_heatEvolve_fourierLp,
  ``Poincare.D12.SpectralSobolev.norm_sin_le_one,
  ``Poincare.D12.SpectralSobolev.poincare_constant_sharp,
  ``Poincare.D12.SpectralSobolev.poincare_wirtinger,
  ``Poincare.D12.SpectralSobolev.poincare_wirtinger_sine,
  ``Poincare.D12.SpectralSobolev.poincare_wirtinger_sine_saturates,
  ``Poincare.D12.SpectralSobolev.sine_wave_hypotheses,
  ``Poincare.D12.SpectralSobolev.sq_eigenvalue_pos,
  ``Poincare.D12.SpectralSobolev.sq_norm_eigenvalue,
  ``Poincare.D12.SpectralSobolev.sq_norm_fourierCoeffOn_deriv_periodic,
  ``Poincare.D12.SpectralSobolev.summable_sq_heatCoeff]

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
