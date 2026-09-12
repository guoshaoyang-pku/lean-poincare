import Lean.Elab.Command
import Poincare.D12.TriangulationTopology.NegControl.NegControl
import Poincare.D7.EvolutionSharp.Implications

open Lean Elab Command

axiom probeAx : False
theorem probeThm : False := probeAx

run_cmd do
  let env ← getEnv
  for n in [`probeThm, `probeAx, `d12NegControlBadTheorem,
            `Poincare.D7.EvolutionSharp.perelmanF_step_lt_old_recovered,
            `Poincare.D7.EvolutionSharp.perelmanF_step_lt_of_one_le] do
    match env.find? n with
    | none => IO.println s!"PROBE {n} MISSING"
    | some ci =>
      IO.println s!"PROBE {n} value?={(ci.value?).isSome}"
      try
        let axs ← Lean.collectAxioms n
        IO.println s!"PROBE {n} collectAxioms={axs.toList}"
      catch _ =>
        IO.println s!"PROBE {n} collectAxioms_error"
