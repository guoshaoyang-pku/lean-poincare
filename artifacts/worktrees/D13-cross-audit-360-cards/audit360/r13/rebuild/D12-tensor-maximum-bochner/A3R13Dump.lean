-- A3 round-13 independent axiom re-audit probe (generated)
-- package: D12-tensor-maximum-bochner
-- imports every module of the cold-rebuilt package
import Poincare.D12.TensorMaximumBochner.Audit
import Poincare.D12.TensorMaximumBochner.BochnerIdentity
import Poincare.D12.TensorMaximumBochner.PositivityPreservation
import Poincare.D12.TensorMaximumBochner.So3Model
import Poincare.D12.TensorMaximumBochner.So3Polynomial
import Poincare.D12.TensorMaximumBochner.So3RicciFlow
import Poincare.D12.TensorMaximumBochner.TangentCone
import Poincare.D12.TensorMaximumBochner.TensorCalculus

open Lean Elab Command

namespace A3R13

axiom a3r13FakeAxiom : True
opaque a3r13FakeOpaque : True
theorem a3r13UsesFakeAxiom : True := a3r13FakeAxiom
theorem a3r13UsesFakeOpaque : True := a3r13FakeOpaque

def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

def dump (roots : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if roots.any (fun r => r.isPrefixOf n) then
      let axs ← Lean.collectAxioms n
      logInfo m!"A3R13|CONST|{n}|{kindOf ci}|{axs.toList.map Name.toString}"

/-- Instrument self-test: both controls must produce a non-empty cone naming the
fake constant. -/
def controls : CommandElabM Unit := do
  for n in [``a3r13UsesFakeAxiom, ``a3r13UsesFakeOpaque] do
    let axs ← Lean.collectAxioms n
    logInfo m!"A3R13|CONTROL|{n}|{axs.toList.map Name.toString}"

end A3R13

run_cmd A3R13.dump [`Poincare.D12]
run_cmd A3R13.controls
