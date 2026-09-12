-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.TensorMaximumBochner.Audit
import Poincare.D12.TensorMaximumBochner.BochnerIdentity
import Poincare.D12.TensorMaximumBochner.PositivityPreservation
import Poincare.D12.TensorMaximumBochner.So3Model
import Poincare.D12.TensorMaximumBochner.So3Polynomial
import Poincare.D12.TensorMaximumBochner.So3RicciFlow
import Poincare.D12.TensorMaximumBochner.TangentCone
import Poincare.D12.TensorMaximumBochner.TensorCalculus

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.TensorMaximumBochner.Audit.d12_kernel_tangent_necessary_audited,
  ``Poincare.D12.TensorMaximumBochner.FeasibleDirection,
  ``Poincare.D12.TensorMaximumBochner.KernelTangent,
  ``Poincare.D12.TensorMaximumBochner.StrictKernelTangent,
  ``Poincare.D12.TensorMaximumBochner.adjugate_eq_det_smul_inv,
  ``Poincare.D12.TensorMaximumBochner.adjugate_posSemidef,
  ``Poincare.D12.TensorMaximumBochner.continuous_dotProduct_mulVec,
  ``Poincare.D12.TensorMaximumBochner.counterexampleA,
  ``Poincare.D12.TensorMaximumBochner.counterexampleA_posSemidef,
  ``Poincare.D12.TensorMaximumBochner.counterexample_kernelTangent,
  ``Poincare.D12.TensorMaximumBochner.counterexample_nondegenerate,
  ``Poincare.D12.TensorMaximumBochner.counterexample_not_feasible,
  ``Poincare.D12.TensorMaximumBochner.dotProduct_mulVec_sq,
  ``Poincare.D12.TensorMaximumBochner.hamiltonField,
  ``Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent,
  ``Poincare.D12.TensorMaximumBochner.hamiltonField_kernel_witness,
  ``Poincare.D12.TensorMaximumBochner.hamiltonField_not_strengthened,
  ``Poincare.D12.TensorMaximumBochner.kernelTangent_not_feasible,
  ``Poincare.D12.TensorMaximumBochner.kernelTangent_of_feasibleDirection,
  ``Poincare.D12.TensorMaximumBochner.kernelTangent_of_posSemidef_path]

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
