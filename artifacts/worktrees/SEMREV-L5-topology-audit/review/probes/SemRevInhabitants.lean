/- SEMREV-L5: kernel-checked inhabitants of the I7 predicates that the L5 card
   calls "uninhabited" (§8 / research brief).

All declarations here are in the SEMREV review namespace, not in the release.
They compile against the L5 union-release oleans (read-only). -/
import Audit.CounterexampleAudit
import Poincare.Longrun.Evolution.Bridge

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace SemRevInhabitants

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Entropy
open Poincare.Longrun.Evolution

universe w

variable {ι : Type w} [Fintype ι]

/-- The L5 §8 claim "no inhabitant of `FiniteMeshConvergence` exists" is refuted by the
release's own D4 non-vacuity witness: concrete mesh `1/(n+1)`, constant state `0`. -/
theorem finiteMeshConvergence_inhabited :
    FiniteMeshConvergence (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (fun _ (_ : Fin 1) => (0 : ℝ)) (fun _ => (0 : ℝ)) :=
  D4Audit.finiteMeshConvergence_nonvacuous

/-- The L5 §8 claim "no inhabitant of `FiniteRepresentsContinuousPerelman` exists" is
refuted by the `identification` field of the release's D4 non-vacuity witness. -/
theorem finiteRepresentsContinuousPerelman_inhabited
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {T : ℝ}
    {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    FiniteRepresentsContinuousPerelman
      (X := ι) (μ := (Measure.count : Measure ι))
      (fun t => finiteReactionEntropyData c (traj t)) c traj T :=
  (D4Audit.perelmanApproximation_nonvacuous F hc ev).some.identification

/-- The L5 research brief calls `ContinuousPerelmanFMonotonicity` statement-only with no
inhabitant; the release proves it at the D4 toy parameters. -/
theorem continuousPerelmanFMonotonicity_inhabited :
    ContinuousPerelmanFMonotonicity
      (fun t => finiteReactionEntropyData (fun _ : Fin 1 => (1 : ℝ))
        ((fun s (_ : Fin 1) => s) t)) 1 :=
  D4Audit.transfer_nonvacuous

end SemRevInhabitants
